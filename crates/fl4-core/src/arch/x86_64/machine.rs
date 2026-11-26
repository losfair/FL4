macro_rules! arch_machine_methods {
    () => {};
}

/// A set of cores, bit `c` for core `c`: x86-64 starts at most 64.
pub type CoreMask = u64;

/// The mask of core `cpu` alone.
#[inline(always)]
pub const fn core_bit(cpu: u64) -> CoreMask {
    1u64 << (cpu & 63)
}
