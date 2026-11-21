/-- FL4's `call_kernel` from the syscall event. -/
theorem gk_fl4CallKernel_sys (rep : Bool) (c : Syscall) : GK (fl4CallKernel (Z := Unit) rep (.syscallEvent c)) := by
  unfold fl4CallKernel
  exact gk_bind (gke_handleE (gk_fl4HandleEvent_sys rep c) fun _ => gke_withoutPreemption gk_preemptionPath)
    fun _ => gk_bind gk_fl4Awaken fun _ => gk_bind gk_schedule fun _ => gk_activateThread

/-- FL4's `call_kernel` from the interrupt event. -/
theorem gk_fl4CallKernel_irq (rep : Bool) : GK (fl4CallKernel (Z := Unit) rep .interrupt) := by
  unfold fl4CallKernel
  exact gk_bind (gke_handleE (gk_fl4HandleEvent_irq rep) fun _ => gke_withoutPreemption gk_preemptionPath)
    fun _ => gk_bind gk_fl4Awaken fun _ => gk_bind gk_schedule fun _ => gk_activateThread

/-- **The syscall entry keeps every `GK` predicate.** -/
theorem gk_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    GK (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact gk_bind (gk_gets _) fun ct => gk_bind (gk_fl4SyscallFaultIP ct) fun _ => gk_fl4CallKernel_sys rep c
