//! The native engine of the differential (`docs/design/m2-dev-backend.md`
//! §5, §10 M2-0): FMIR → OIR (`fors-oir`) → stencils (`fors-codegen-dev`) →
//! a signed `MH_EXECUTE` (`fors-link`, `fors-obj`) → written to a scratch
//! directory → spawned with an EMPTY environment, stdin `/dev/null`, a 10 s
//! timeout → a [`NativeRecord`].
//!
//! Compiling is pure Rust and runs everywhere; only macOS/aarch64 can
//! execute the image (elsewhere a run is a `spawn-fail`, and every native
//! test is gated on the target).

use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use fors_codegen_dev::rt::{ENTRY, FORS_MAIN};
use fors_oir::{FmirInput, Refusal};

use crate::Candidate;

/// The per-run timeout (§5).
pub const TIMEOUT: Duration = Duration::from_secs(10);
/// `SIGTRAP`: a Fors trap's `brk` with no handler installed (the handler and
/// its stderr line arrive in M2-3).
pub const SIGTRAP: i32 = 5;
/// The image's file name; also its code-signature identifier, so it is
/// fixed (renaming the output changes the bytes, §4.2).
pub const IMAGE_NAME: &str = "prog";

/// How a native run ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeExit {
    Status(i32),
    Signal(i32),
    Timeout,
}

/// §5's native record: exit, stdout bytes, stderr bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeRecord {
    pub exit: NativeExit,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

/// Per-phase microseconds of one compile (§10 M2-0 "Report").
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Phases {
    pub oir: u64,
    pub select: u64,
    pub emit: u64,
    pub link: u64,
    pub sign: u64,
    pub write: u64,
}

impl Phases {
    pub fn line(&self) -> String {
        format!(
            "oir {}us | select {}us | emit {}us | link {}us | sign {}us | write {}us",
            self.oir, self.select, self.emit, self.link, self.sign, self.write
        )
    }
}

/// A compile that produced no image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileFail {
    /// A precise refusal by name (out of the M2-0 subset).
    Refused(Refusal),
    /// The backend panicked, or the link failed: always a backend bug.
    Panicked(String),
}

/// A compiled image.
#[derive(Clone, Debug)]
pub struct Compiled {
    pub image: Vec<u8>,
    pub phases: Phases,
}

fn us(t: Instant) -> u64 {
    t.elapsed().as_micros() as u64
}

fn compile_inner(c: &Candidate) -> Result<Compiled, CompileFail> {
    let f = c
        .prog
        .fns
        .get(c.prog.entry)
        .ok_or_else(|| CompileFail::Panicked("no entry function".into()))?;
    let mut ph = Phases::default();
    let t = Instant::now();
    let oir = fors_oir::from_fmir(&FmirInput {
        decl: &f.decl,
        tys: &c.tys,
        strings: &f.strings,
        intrinsics: &f.intrinsics,
    })
    .map_err(CompileFail::Refused)?;
    if let Err(e) = fors_oir::verify(&oir) {
        return Err(CompileFail::Panicked(format!(
            "from_fmir produced invalid OIR: {e}"
        )));
    }
    ph.oir = us(t);
    let t = Instant::now();
    let lir = fors_codegen_dev::select::select(&oir).map_err(CompileFail::Refused)?;
    ph.select = us(t);
    let t = Instant::now();
    let atom = fors_codegen_dev::emit::emit(&lir, &oir, FORS_MAIN).map_err(CompileFail::Refused)?;
    ph.emit = us(t);
    let t = Instant::now();
    let linked = fors_link::place(&[atom], &fors_codegen_dev::runtime_atoms(), ENTRY)
        .map_err(|e| CompileFail::Panicked(e.to_string()))?;
    let layout = fors_link::image_layout(&linked, IMAGE_NAME);
    ph.link = us(t);
    let t = Instant::now();
    let image = fors_obj::sign::sign(layout, IMAGE_NAME);
    ph.sign = us(t);
    Ok(Compiled { image, phases: ph })
}

/// Compiles `c`'s entry function into a signed image, catching a backend
/// panic as [`CompileFail::Panicked`].
pub fn compile(c: &Candidate) -> Result<Compiled, CompileFail> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| compile_inner(c))) {
        Ok(r) => r,
        Err(p) => Err(CompileFail::Panicked(crate::panic_text(&*p))),
    }
}

/// A scratch directory that native runs write their image into (one per
/// worker thread; removed on drop).
pub struct Runner {
    dir: PathBuf,
}

static RUNNER_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

impl Runner {
    pub fn new() -> std::io::Result<Runner> {
        let n = RUNNER_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!("fors-native-{}-{n}", std::process::id()));
        std::fs::create_dir_all(&dir)?;
        Ok(Runner { dir })
    }

    /// Writes `image` (a new inode every time) and runs it; also returns
    /// the write's microseconds. `Err` is a spawn failure.
    pub fn run(&self, image: &[u8]) -> Result<(NativeRecord, u64), String> {
        let t = Instant::now();
        let path = fors_obj::write::write_executable(&self.dir, IMAGE_NAME, image)
            .map_err(|e| format!("write: {e}"))?;
        let write_us = us(t);
        let mut child = Command::new(&path)
            .env_clear()
            .current_dir(&self.dir)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("spawn: {e}"))?;
        let mut out = child.stdout.take().expect("piped");
        let mut err = child.stderr.take().expect("piped");
        let out_t = std::thread::spawn(move || {
            let mut b = Vec::new();
            let _ = out.read_to_end(&mut b);
            b
        });
        let err_t = std::thread::spawn(move || {
            let mut b = Vec::new();
            let _ = err.read_to_end(&mut b);
            b
        });
        let start = Instant::now();
        let mut nap = Duration::from_micros(50);
        let status = loop {
            match child.try_wait() {
                Ok(Some(s)) => break Some(s),
                Ok(None) if start.elapsed() >= TIMEOUT => {
                    let _ = child.kill();
                    let _ = child.wait();
                    break None;
                }
                Ok(None) => {
                    std::thread::sleep(nap);
                    nap = (nap * 2).min(Duration::from_millis(5));
                }
                Err(e) => return Err(format!("wait: {e}")),
            }
        };
        let stdout = out_t.join().unwrap_or_default();
        let stderr = err_t.join().unwrap_or_default();
        let exit = match status {
            None => NativeExit::Timeout,
            Some(s) => match s.code() {
                Some(c) => NativeExit::Status(c),
                None => NativeExit::Signal(signal_of(&s)),
            },
        };
        Ok((
            NativeRecord {
                exit,
                stdout,
                stderr,
            },
            write_us,
        ))
    }
}

#[cfg(unix)]
fn signal_of(s: &std::process::ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    s.signal().unwrap_or(-1)
}

#[cfg(not(unix))]
fn signal_of(_: &std::process::ExitStatus) -> i32 {
    -1
}

impl Drop for Runner {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// Compile and run `c` once (a fresh scratch directory).
pub fn run(c: &Candidate) -> Result<NativeRecord, String> {
    let img = compile(c).map_err(|e| format!("{e:?}"))?;
    let r = Runner::new().map_err(|e| e.to_string())?;
    r.run(&img.image).map(|(rec, _)| rec)
}
