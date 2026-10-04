//! Writing an image to disk: a temporary file in the TARGET directory (so the
//! rename never crosses a filesystem), mode `0o755`, then `rename` over the
//! output. The output is always a NEW inode — `spikes/macho-resign` showed
//! that patching an inode the kernel has already executed is SIGKILLed
//! non-deterministically.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

/// Writes `bytes` to `dir/name` atomically and returns the path.
pub fn write_executable(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<PathBuf> {
    let out = dir.join(name);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let tmp = dir.join(format!(".{name}.tmp{}-{n}", std::process::id()));
    std::fs::write(&tmp, bytes)?;
    set_executable(&tmp)?;
    std::fs::rename(&tmp, &out)?;
    Ok(out)
}

#[cfg(unix)]
fn set_executable(p: &Path) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(p, std::fs::Permissions::from_mode(0o755))
}

#[cfg(not(unix))]
fn set_executable(_: &Path) -> io::Result<()> {
    Ok(())
}
