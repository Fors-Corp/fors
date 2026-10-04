//! `fors-obj`: the dev backend's Mach-O writer (`docs/design/m2-dev-backend.md`
//! §4), ported from `spikes/aarch64-macho` into a tested crate. Zero
//! dependencies, no `unsafe`, no timestamps, no host paths, every table
//! sorted: an image is a pure function of its inputs.
//!
//! - [`atom`]: the unit the backend emits and the linker places;
//! - [`macho`]: header, segments, load commands (§4.1 minus `__DATA*`);
//! - [`fixups`]: the (empty, in M2-0) chained-fixups payload;
//! - [`trie`]: the exports trie;
//! - [`sign`]: the ad-hoc CodeDirectory (§4.2) and its pure-Rust check;
//! - [`uuid`]: the content-derived UUID from page hashes (§4.2, E7);
//! - [`sha256`]: in-house SHA-256;
//! - [`write`]: temp file, `0o755`, `rename`;
//! - [`scan`]: read-back for tests and image scans.

#![deny(unsafe_code)]

pub mod atom;
pub mod fixups;
pub mod macho;
pub mod scan;
pub mod sha256;
pub mod sign;
pub mod trie;
pub mod uuid;
pub mod write;

pub use atom::{Atom, Reloc, TrapRow};
pub use macho::{ExecSpec, build_executable};
