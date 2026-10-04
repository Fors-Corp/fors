//! ch02 R4's failure ABI — constants only in M2-0. The classifier
//! `failure_class(payload_size)` (a PLAN §5 contribution point, owner Q7)
//! lands in M2-5 with its gate `failure_class_table_0_to_64`.

/// A raising function's payload (`max(size_of T, size_of E)`) travels in
/// `x0..x2` when it is at most this many bytes, else through `sret` in `x8`.
pub const FAILURE_INLINE_MAX: u32 = 24;

/// The success/failure tag register: `x9`, `0` = success.
pub const FAILURE_TAG_REG: u8 = 9;

#[cfg(test)]
mod tests {
    #[test]
    fn inline_payload_fits_the_three_result_registers() {
        assert_eq!(super::FAILURE_INLINE_MAX, 3 * 8);
        assert_eq!(super::FAILURE_TAG_REG, 9);
    }
}
