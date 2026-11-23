/// `Arch::msi_map`'s answers.
pub mod msi {
    pub const OK: u64 = 0;
    /// No ITS, or no table left for another device.
    pub const NO_ITS: u64 = 1;
    pub const BAD_DEVICE: u64 = 2;
    /// Out of range, or mapped already.
    pub const BAD_EVENT: u64 = 3;
}

macro_rules! arch_machine_methods {
    () => {
        /// AArch64 cache maintenance (seL4 `doFlush`): operation `op`
        /// (`vspace::CACHE_*`) over `len` bytes at `vaddr` in the address space
        /// `root` with ASID `asid`, physically at `paddr`.
        fn cache_op(&mut self, op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64);
        /// AArch64: hardware sets access flags (TCR_EL1.HA), so a cleared flag
        /// does not fault.
        fn hw_access_flag(&self) -> bool;
        /// AArch64: the largest SPI the interrupt controller has.
        fn max_spi(&self) -> u64;
        /// AArch64: configure interrupt `irq` as edge (true) or level triggered
        /// and, for an SPI, route it to `core`.
        fn configure_irq(&mut self, irq: u64, edge: bool, core: u64);
        /// AArch64: map event `event` of device `device` to LPI `irq` on
        /// `core` through the ITS (`msi::OK`), or refuse and change nothing
        /// (another `msi` code). `irq_free` unmaps it.
        fn msi_map(&mut self, _irq: u64, _device: u64, _event: u64, _core: u64) -> u64 { msi::NO_ITS }
        /// AArch64 Stage-2 IPA width (40, 44, or 48).
        fn s2_ipa_bits(&self) -> u64 { 40 }
        /// AArch64: install Stage-2 root (kernel VA, 0 = empty root) & ASID into VTTBR_EL2.
        fn set_stage2_vspace(&mut self, _root: u64, _asid: u64) {}
        /// AArch64: invalidate Stage-2 TLB for one IPA in `asid`.
        fn invalidate_stage2_page(&mut self, _asid: u64, _ipa: u64) {}
        /// AArch64: invalidate all Stage-1+Stage-2 TLB entries for `asid`'s VMID.
        fn invalidate_stage2_vmid(&mut self, _asid: u64) {}
        /// AArch64: flush a VCPU's live hardware state back into its object and release ownership.
        fn vcpu_flush(&mut self, _vcpu: u64) {}
        /// AArch64: flush a VCPU's live hardware state needed for `mask` (subset of `vcpu_state_mask`).
        fn vcpu_flush_state(&mut self, vc: u64, _mask: u64) {
            self.vcpu_flush(vc);
        }
        /// AArch64: hardware VGIC type register (`ICH_VTR_EL2` / `GICH_VTR`).
        fn vcpu_vgic_vtr(&self) -> u64 { 0 }
        /// AArch64: GIC version (2 or 3).
        fn vcpu_gic_version(&self) -> u64 { 3 }
        /// AArch64: boot core `MIDR_EL1` for `VPIDR_EL2` default.
        fn vcpu_midr(&self) -> u64 { 0 }
    };
}
