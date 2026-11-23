/-
P1: InvGaps' `vcpu` family (`vcpu.decode`), by label.  After the VCPU's
stall, the invariants are `Cur0` from the decode's start; the labels write
VCPU words (untracked object words, `QueueVcpu`), the TCBs' VCPU words, the
caller's message registers and IPC buffer (`reply`), an I/O-port cap's slot,
and end with the caller restarted or set running.
-/
import Fl4Proofs.P1.QueueVcpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {P3Ok : S → Prop}
variable {H : Heap} {Cs Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

/-- `Cur0` at a decode's start. -/
theorem Cur0.ofPre {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac s cap extra) :
    Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s := by
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  refine ⟨D.hcsc, Ac, D.bxi, rfl, rfl, Or.inl rfl, fun y hy e => ?_, nbr_runnable D.run, WritesIn.refl _ _⟩
  rw [D.act] at e; exact notT_small hT (by simp) (e ▸ hy)

/-- An error leaf. -/
theorem err_leaf {A : Type _} {s0 sX : S} {aX : A} {r : core.result.Result Unit error.Exc}
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 sX) (hr : r ≠ .Err .Preempted) :
    (ok (r, sX, aX) : Result _) ⦃ r s' _ => DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 r s' ⦄ := by
  obtain ⟨Ac', hb⟩ := h.bxi
  exact (WP.spec_ok _).2 (DecPost.of_bxi hb hr)

/-- The caller restarted. -/
theorem restart_leaf {A : Type _} {s0 sX : S} {aX : A} {ct : U64}
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 sX) (ect : ct = L.curW sX) :
    (do
      let s2 ← sched.set_thread_state st sX ct sched.TS_RESTART
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, aX)) ⦃ r s' _ =>
        DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 r s' ⦄ := by
  subst ect
  obtain ⟨Ac', hb⟩ := h.bxi
  have hct : L.curW sX ∈ H.tcbs := hb.1.choose_spec.choose_spec.curT
  have nb := h.nb
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) sX _ hb.blk hct (fun hb' => nb (Or.inl hb'))
    (fun e => nb (Or.inr e))) ?_
  rintro s2 ⟨h2, -⟩
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))


/-- A reply to the caller, then a success. -/
theorem reply_leaf {A : Type _} (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) {s0 sX : S} {aX : A}
    {call : Bool} {val : U64} (he : EntAt st P3Ok s0) (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 sX)
    (hU : UserOK st H.tcbs Cs H.omega H U sX) :
    (do
      let s3 ← vcpu.reply st sX call val
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, aX)) ⦃ r s' _ =>
        DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 r s' ⦄ := by
  obtain ⟨Ac1, hX⟩ := h.bxi
  obtain ⟨Q, R, x0⟩ := BXI.xs hX hU
  have hct : L.curW sX ∈ H.tcbs := hX.1.choose_spec.choose_spec.curT
  have nb := h.nb
  have NB : ∀ s', XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R sX s' →
      ¬ BlockedR (L.mem s' (stA (L.curW sX))) := fun s' x => by
    rw [stA_eq, x.1.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp), ← stA_eq]; exact nb
  unfold vcpu.reply
  refine WP.spec_bind (Pₘ := fun s3 => BXI st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac1 s3)
    (WP.spec_bind (sched.cur_thread.spec sX) fun ct ect => ?_) fun s3 h3 => (WP.spec_ok _).2 (DecPost.ok_bxi h3)
  have e : ct = L.curW sX := ect
  subst e
  refine WP.spec_bind (Pₘ := fun s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R sX s') ?_
    fun s1 x1 => sched.set_thread_state.running_nbr x1.bxi hct (NB _ x1)
  split
  · refine WP.spec_bind (E.buf _ _ _ _ sX _ ⟨s0, he, h.fr⟩ x0.1 hct) fun b hb => ?_
    refine WP.spec_bind (msg.set_mr.xsv (XSV.start x0) hct hb (by simp)) ?_
    rintro ⟨_, s2⟩ ⟨x2, -⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (obj.Tcb.set_reg.xsv (v := 0#u64) x2 hct (by simp [layout.reg.BADGE, layout.reg.RDI]))
      fun s3 x3 => ?_
    refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
    unfold msg.set_msg_info
    exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
      obj.Tcb.set_reg.xsv (v := w) x3 hct (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
  · exact (WP.spec_ok _).2 (XSV.start x0)


theorem Cur0.curW_eq {s0 s : S} (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    L.curW s = L.curW s0 := h.2.choose_spec.2.1

theorem vcpu.decode_loop0.cur0 (hH : HeapOK H) {s0 s : S} {v buf ct i : U64} (hv : H v = some (.other 15))
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    vcpu.decode_loop0 st s v buf ct i ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_loop0
  apply loop.spec_decr_nat (measure := fun y => 15 - y.2.val)
    (inv := fun y => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold vcpu.decode_loop0.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 15 := by simpa using hj
    refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ hS) fun val _ => ?_
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    refine WP.spec_bind (vcpu.set.cur0 hH hv (o := i2) (x := val)
      (by simp [vcpu.REGS] at hi2; omega) (by simp [vcpu.REGS] at hi2; omega) h1) fun s2 h2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

/-- The VCPU's stall writes node words only. -/
theorem vcpu.stall.node {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} (a : A) (v : U64)
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    vcpu.stall st ar s a v ⦃ s1 _ => WritesIn st s s1 (NodeW st s) ⦄ := by
  obtain ⟨Ac', hX⟩ := h.bxi
  unfold vcpu.stall
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun t _ => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec t) fun b _ => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · exact WP.spec_mono (smp.remote_tcb_stall.bxi hA s a1 t hX) fun r ⟨_, _, _, _, _, _, _, w⟩ => w

theorem vcpu.write_vmcs.cur0 (hH : HeapOK H) {s0 s : S} {v f x : U64} (hv : H v = some (.other 15))
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    vcpu.write_vmcs st s v f x ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ∧
      L.ksb s' = L.ksb s ⦄ := by
  unfold vcpu.write_vmcs
  refine WP.spec_bind (vcpu.vmcs_addr.off v f) ?_
  rintro _ ⟨o, ho, h8, rfl⟩
  exact WP.spec_mono (LawfulStore.write_spec s _ x) fun s' e => e ▸
    ⟨h.vword hH hv (by omega) h8, L.ksb_wr _ _ _⟩

set_option maxHeartbeats 8000000 in
/-- `sanitize_vmcb` accepts only VMCB words (aligned, below 2048). -/
theorem vcpu.sanitize_vmcb.off {A : Type _} {ar : machine.Arch A} (a : A) (f old value : U64)
    (hf : ¬ (f.val < 2048 ∧ f.val % 8 = 0)) :
    vcpu.sanitize_vmcb ar a f old value ⦃ r => ∃ e, r = .Err e ⦄ := by
  unfold vcpu.sanitize_vmcb
  split
  all_goals first
    | (exfalso; apply hf; constructor <;> decide)
    | (simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 ⟨_, rfl⟩)
    | skip


theorem vcpu.decode_loop1.xs {s0 s : S} {v ct f value b i n : U64} {Ac1 : Set U64}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (hval : value.val ≤ 64)
    (h : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 s) (hc : ct ∈ H.tcbs) (hb : BufOK U b) :
    vcpu.decode_loop1 st s v ct f value b i n ⦃ r => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_loop1
  apply loop.spec_decr_nat (measure := fun y => 64 - y.2.1.val)
    (inv := fun y => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 y.1)
  · rintro ⟨s1, j, m⟩ h1
    simp only at h1
    try dsimp only
    unfold vcpu.decode_loop1.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 64 := by have : j.val < value.val := by simpa using hj
                                omega
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.vcpu.vmcb_hidden.p0 _) fun hid _ => ?_
    refine WP.spec_bind (Pₘ := fun _ => True) (by
      split
      · exact (WP.spec_ok _).2 trivial
      · refine WP.spec_bind (vcpu.svm.RAX.spec) fun _ _ => ?_
        split
        · exact vcpu.get.any _ _ _
        · exact vcpu.get.any _ _ _) fun val _ => ?_
    refine WP.spec_bind (msg.set_mr.xsv (v := val) h1 hc hb (by omega)) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    try simp only [uncurry_apply_pair]
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem vcpu.decode_loop2.xs {s0 s : S} {v ct f value b i n : U64} {Ac1 : Set U64}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (hval : value.val ≤ 64)
    (h : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 s) (hc : ct ∈ H.tcbs) (hb : BufOK U b) :
    vcpu.decode_loop2 st s v ct f value b i n ⦃ r => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_loop2
  apply loop.spec_decr_nat (measure := fun y => 64 - y.2.1.val)
    (inv := fun y => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 y.1)
  · rintro ⟨s1, j, m⟩ h1
    simp only at h1
    try dsimp only
    unfold vcpu.decode_loop2.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 64 := by have : j.val < value.val := by simpa using hj
                                omega
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.vcpu.vmcb_hidden.p0 _) fun hid _ => ?_
    refine WP.spec_bind (Pₘ := fun _ => True) (by
      split
      · exact (WP.spec_ok _).2 trivial
      · refine WP.spec_bind (vcpu.svm.RAX.spec) fun _ _ => ?_
        split
        · exact vcpu.get.any _ _ _
        · exact vcpu.get.any _ _ _) fun val _ => ?_
    refine WP.spec_bind (msg.set_mr.xsv (v := val) h1 hc hb (by omega)) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    try simp only [uncurry_apply_pair]
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

/-- The caller set running after an `XS` stretch from a `Cur0` state, then a success. -/
theorem running_leaf {A : Type _} {s0 sX sY : S} {aY : A} {Ac1 : Set U64} {Q : U64 → U64 → List U64}
    {R : U64 → List U64} {ct : U64}
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 sX)
    (x : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R sX sY) (ect : ct = L.curW sX) :
    (do
      let s5 ← sched.set_thread_state st sY ct sched.TS_RUNNING
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, aY)) ⦃ r s' _ =>
        DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 r s' ⦄ := by
  subst ect
  obtain ⟨Ac', hX⟩ := h.bxi
  have hct : L.curW sX ∈ H.tcbs := hX.1.choose_spec.choose_spec.curT
  have nb : ¬ BlockedR (L.mem sY (stA (L.curW sX))) := by
    rw [stA_eq, x.1.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp), ← stA_eq]; exact h.nb
  refine WP.spec_bind (sched.set_thread_state.running_nbr x.bxi hct nb) fun s5 h5 => ?_
  exact (WP.spec_ok _).2 (DecPost.ok_bxi h5)

theorem vcpu.set.cur0k (hH : HeapOK H) {s0 s : S} {v o x : U64} (hv : H v = some (.other 15))
    (ho : o.val < 2 ^ 15) (h8 : o.val % 8 = 0) (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    vcpu.set st s v o x ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ∧ L.ksb s' = L.ksb s ⦄ := by
  unfold vcpu.set
  simp only [lift, bind_ok]
  exact WP.spec_mono (LawfulStore.write_spec s _ x) fun s' e => e ▸ ⟨h.vword hH hv ho h8, L.ksb_wr _ _ _⟩

/-- A VCPU word's address. -/
def VWord (v x : U64) : Prop := ∃ k : U64, k.val < 2 ^ 15 ∧ k.val % 8 = 0 ∧ x = core.num.U64.wrapping_add v k

set_option maxHeartbeats 4000000 in
/-- `msr_addr` names a VCPU word. -/
theorem vcpu.msr_addr.off (v f : U64) (amd : Bool) :
    vcpu.msr_addr v f amd ⦃ o => ∀ x, o = some x → VWord v x ⦄ := by
  unfold vcpu.msr_addr
  split
  · simp only [lift, bind_ok]
    exact (WP.spec_ok _).2 fun x e => ⟨vcpu.XCR0, by simp [vcpu.XCR0], by simp [vcpu.XCR0], by cases e; rfl⟩
  split
  · unfold vcpu.svm_msr
    split
    all_goals first
      | (simp only [core.option.Option.map, bind_ok]; exact (WP.spec_ok _).2 fun x e => by cases e)
      | (step as ⟨k, ek⟩
         simp only [core.option.Option.map, bind_ok, vcpu.msr_addr.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64,
           vcpu.msr_addr.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once]
         refine WP.spec_bind (Pₘ := fun m => m = core.num.U64.wrapping_add v k) ((WP.spec_ok _).2 rfl) fun m em => ?_
         subst em
         exact (WP.spec_ok _).2 fun x e => by
           cases e; exact ⟨k, by rw [ek]; simp, by rw [ek]; simp, rfl⟩)
  split
  · simp only [lift, bind_ok]
    exact (WP.spec_ok _).2 fun x e => ⟨vcpu.CR2, by simp [vcpu.CR2], by simp [vcpu.CR2], by cases e; rfl⟩
  unfold vcpu.msr_slot
  split
  all_goals first
    | (simp only [core.option.Option.map, bind_ok]; exact (WP.spec_ok _).2 fun x e => by cases e)
    | (simp only [core.option.Option.map, bind_ok, lift, vcpu.msr_addr.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64,
         vcpu.msr_addr.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once]
       refine WP.spec_bind (Pₘ := fun m => m = core.num.U64.wrapping_add
         (core.num.U64.wrapping_add v vcpu.MSRS) (core.num.U64.wrapping_mul _ 8#u64)) ((WP.spec_ok _).2 rfl)
         fun m em => ?_
       subst em
       refine (WP.spec_ok _).2 fun x e => ?_
       cases e
       refine ⟨_, ?_, ?_, wadd_assoc _ _ _ ?_⟩
       all_goals simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
         vcpu.MSRS])

/-- An MSR word written, read back and replied. -/
theorem msr_wleaf {A : Type _} (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) (hH : HeapOK H)
    {s0 sX : S} {aX : A} {call : Bool} {v x value : U64} (hv : H v = some (.other 15)) (hx : VWord v x)
    (he : EntAt st P3Ok s0) (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 sX) (hU : UserOK st H.tcbs Cs H.omega H U sX) :
    (do
      let s2 ← st.write sX x value
      let i3 ← st.read s2 x
      let s3 ← vcpu.reply st s2 call i3
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, aX)) ⦃ r s' _ =>
        DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 r s' ⦄ := by
  obtain ⟨k, hk, h8, rfl⟩ := hx
  refine WP.spec_bind (LawfulStore.write_spec sX _ value) fun s2 e2 => ?_
  subst e2
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun i3 _ => ?_
  exact reply_leaf E he (h.vword hH hv hk h8) (hU.ksb (L.ksb_wr _ _ _))

/-- A word read and replied. -/
theorem read_rleaf {A : Type _} (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok)
    {s0 sX : S} {aX : A} {call : Bool} {x : U64}
    (he : EntAt st P3Ok s0) (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 sX) (hU : UserOK st H.tcbs Cs H.omega H U sX) :
    (do
      let i2 ← st.read sX x
      let s2 ← vcpu.reply st sX call i2
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, aX)) ⦃ r s' _ =>
        DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 r s' ⦄ :=
  WP.spec_bind (LawfulStore.read_spec _ _) fun _ _ => reply_leaf E he h hU

/-- A VCPU object's word is an object word off the frame words. -/
theorem vcpu_obj_om (hH : HeapOK H) {v o : U64} (hv : H v = some (.other 15)) (ho : o.val < 2 ^ 15)
    (h8 : o.val % 8 = 0) :
    core.num.U64.wrapping_add v o ∈ H.omega ∧ core.num.U64.wrapping_add v o ∉ H.frame := by
  rcases (vcpu_obj_capw hH hv ho h8 : CapW H.tcbs H.omega H.frame _) with ⟨t, ht, K, hK, e⟩ | h
  · -- a TCB's low words are not in a VCPU object
    exfalso
    have hal := hH.align v _ hv
    have hfit := hH.fits v _ hv
    rw [show (HKind.other 15).bits = 15 from rfl] at hal hfit
    have hb : (core.num.U64.wrapping_add v o).val = v.val + o.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have ht' : H t = some .tcb := ht
    have hne : t ≠ v := by rintro rfl; rw [hv] at ht'; cases ht'
    have tf := hH.fits t _ ht'
    rw [show (HKind.tcb).bits = 12 from rfl] at tf
    have hv2 : (core.num.U64.wrapping_add t K).val = t.val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := hH.disj v (.other 15) t .tcb hv ht' hne.symm
    rw [show (HKind.other 15).bits = 15 from rfl, show (HKind.tcb).bits = 12 from rfl] at this
    have ev := congrArg UScalar.val e
    rw [hb, hv2] at ev
    omega
  · exact h

theorem ioW_eq (v k : U64) (hk : k.val < 8192) :
    ioW v k = core.num.U64.wrapping_add v (core.num.U64.wrapping_add vcpu.IO k) :=
  wadd_assoc _ _ _ (by simp [vcpu.IO]; omega)

theorem io_off {k : U64} (hk : k.val < 8192) : (core.num.U64.wrapping_add vcpu.IO k).val = 24576 + k.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vcpu.IO]; omega

set_option maxHeartbeats 4000000 in
/-- **The VCPU list's placement from the VCPU objects' placement.** -/
theorem VcpuPl.ioPl {s0 : S} (P : VcpuPl st H Cs Rp Scs Nt Z s0) :
    IoPortPlaceAt st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z s0 := by
  have hH := P.heap
  have obj : ∀ {v : U64}, H v = some (.other 15) → v.val % 2 ^ 15 = 0 ∧ v.val + 2 ^ 15 ≤ 2 ^ 64 :=
    fun {v} hv => ⟨hH.align v _ hv, hH.fits v _ hv⟩
  have wv : ∀ {v o : U64}, H v = some (.other 15) → o.val < 2 ^ 15 →
      (core.num.U64.wrapping_add v o).val = v.val + o.val := fun {v o} hv ho => by
    have := (obj hv).2
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine ⟨fun Ac s v k hf hX hl hk h8 => ?_, fun Ac s v hf hX hl => ?_, fun Ac s v w k hf hX hl hl' hk h8 => ?_⟩
  · have hv := (P.listed Ac s v hf hX hl).1
    have ho : (core.num.U64.wrapping_add vcpu.IO k).val < 2 ^ 15 := by rw [io_off hk]; omega
    have ho8 : (core.num.U64.wrapping_add vcpu.IO k).val % 8 = 0 := by rw [io_off hk]; omega
    rw [ioW_eq v k hk]
    exact ⟨vcpu_obj_aligned hH hv ho ho8, vcpu_obj_om hH hv ho ho8⟩
  · exact (vcpu_obj_om hH (P.listed Ac s v hf hX hl).1 (o := vcpu.NEXT) (by simp [vcpu.NEXT])
      (by simp [vcpu.NEXT])).1
  · obtain ⟨hv, hks⟩ := P.listed Ac s v hf hX hl
    have hw := (P.listed Ac s w hf hX hl').1
    have ho : (core.num.U64.wrapping_add vcpu.IO k).val < 2 ^ 15 := by rw [io_off hk]; omega
    have hiv : (ioW v k).val = v.val + 24576 + k.val := by
      rw [ioW_eq v k hk, wv hv ho, io_off hk]; omega
    have hnw : (vNextA w).val = w.val + 20488 := by
      unfold vNextA; rw [wv hw (by simp [vcpu.NEXT])]; simp [vcpu.NEXT]
    have q := hX.1.choose_spec.choose_spec
    have hfit := (q.nodes _ q.cur).fits
    unfold LawfulStore.nodeBase at hfit
    have hhd : (vHeadA st s).val = (L.ksb s).val + 80 := by
      unfold vHeadA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, layout.ks.VCPU_HEAD]
      omega
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have ev := congrArg UScalar.val e
      rw [hiv, hnw] at ev
      by_cases hvw : v = w
      · subst hvw; omega
      · have := hH.disj v (.other 15) w (.other 15) hv hw hvw
        rw [show (HKind.other 15).bits = 15 from rfl] at this
        omega
    · have ev := congrArg UScalar.val e
      rw [hiv, hhd] at ev
      omega

theorem vcpu.decode_loop3.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (P : IoPortPlaceAt st T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {first last prior v fuel : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : v = 0#u64 ∨ VListed st s v) :
    vcpu.decode_loop3 st ar s a first last prior v fuel ⦃ s' _ => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_loop3
  apply loop.spec_decr_nat (measure := fun y => y.2.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1 ∧ (y.2.2.1 = 0#u64 ∨ VListed st y.1 y.2.2.1))
  · rintro ⟨s1, a1, v1, f1⟩ ⟨h1, hv1⟩
    simp only
    unfold vcpu.decode_loop3.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hne
    have hv0 : v1 ≠ 0#u64 := by simpa using hne
    have hl : VListed st s1 v1 := hv1.resolve_left hv0
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    step as ⟨f2, hf2⟩
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ VListed st r.1 v1)
      ?_ ?_
    · split
      · refine WP.spec_bind (vcpu.stall.cur0 hA a1 v1 h1) ?_
        rintro ⟨s2, a2⟩ ⟨h2, k2, o2⟩
        try simp only [uncurry_apply_pair]
        obtain ⟨-, Ac1, hX1, -⟩ := id h1
        have hl2 : VListed st s2 v1 := VListed.keep k2
          (o2 _ (hX1.2.2.2.1.ksΩ _ (by simp [layout.ks.VCPU_HEAD]) (by simp [layout.ks.VCPU_HEAD])))
          (fun w hw => o2 _ (P.nxt Ac1 s1 w h1.fr hX1 hw)) hl
        unfold vcpu.ports
        refine WP.spec_bind (vcpu.ports_loop.cur0 (port := first) (high := last) P h2 hl2) ?_
        rintro s3 ⟨h3, hl3, -, -⟩
        exact (WP.spec_ok _).2 ⟨h3, hl3⟩
      · exact (WP.spec_ok _).2 ⟨h1, hl⟩
    rintro ⟨s3, a3⟩ ⟨h3, hl3⟩
    try simp only [uncurry_apply_pair]
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s3 _) fun v2 e2 => ?_
    have hd : v2 = 0#u64 ∨ VListed st s3 v2 := by
      by_cases z : v2 = 0#u64
      · exact Or.inl z
      · right
        have e2' : v2 = L.mem s3 (vNextA v1) := e2
        rw [e2']; exact VListed.next hl3 (e2' ▸ z)
    have hf' : 0 < f1.val := by
      have := hf; simp only [gt_iff_lt] at this; scalar_tac
    exact (WP.spec_ok _).2 ⟨h3, hd, by dsimp only; scalar_tac⟩
  · exact ⟨h, hv⟩

theorem vcpu.decode_loop4.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (P : IoPortPlaceAt st T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {first last prior v fuel : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : v = 0#u64 ∨ VListed st s v) :
    vcpu.decode_loop4 st ar s a first last prior v fuel ⦃ s' _ => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.decode_loop4
  apply loop.spec_decr_nat (measure := fun y => y.2.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1 ∧ (y.2.2.1 = 0#u64 ∨ VListed st y.1 y.2.2.1))
  · rintro ⟨s1, a1, v1, f1⟩ ⟨h1, hv1⟩
    simp only
    unfold vcpu.decode_loop4.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hne
    have hv0 : v1 ≠ 0#u64 := by simpa using hne
    have hl : VListed st s1 v1 := hv1.resolve_left hv0
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    step as ⟨f2, hf2⟩
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ VListed st r.1 v1)
      ?_ ?_
    · split
      · refine WP.spec_bind (vcpu.stall.cur0 hA a1 v1 h1) ?_
        rintro ⟨s2, a2⟩ ⟨h2, k2, o2⟩
        try simp only [uncurry_apply_pair]
        obtain ⟨-, Ac1, hX1, -⟩ := id h1
        have hl2 : VListed st s2 v1 := VListed.keep k2
          (o2 _ (hX1.2.2.2.1.ksΩ _ (by simp [layout.ks.VCPU_HEAD]) (by simp [layout.ks.VCPU_HEAD])))
          (fun w hw => o2 _ (P.nxt Ac1 s1 w h1.fr hX1 hw)) hl
        unfold vcpu.ports
        refine WP.spec_bind (vcpu.ports_loop.cur0 (port := first) (high := last) P h2 hl2) ?_
        rintro s3 ⟨h3, hl3, -, -⟩
        exact (WP.spec_ok _).2 ⟨h3, hl3⟩
      · exact (WP.spec_ok _).2 ⟨h1, hl⟩
    rintro ⟨s3, a3⟩ ⟨h3, hl3⟩
    try simp only [uncurry_apply_pair]
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s3 _) fun v2 e2 => ?_
    have hd : v2 = 0#u64 ∨ VListed st s3 v2 := by
      by_cases z : v2 = 0#u64
      · exact Or.inl z
      · right
        have e2' : v2 = L.mem s3 (vNextA v1) := e2
        rw [e2']; exact VListed.next hl3 (e2' ▸ z)
    have hf' : 0 < f1.val := by
      have := hf; simp only [gt_iff_lt] at this; scalar_tac
    exact (WP.spec_ok _).2 ⟨h3, hd, by dsimp only; scalar_tac⟩
  · exact ⟨h, hv⟩

theorem vcpu.ports_loop.cur0v (hH : HeapOK H) {s0 s : S} {v high : U64} {port : U64} {d : Bool}
    (hv : H v = some (.other 15)) (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    vcpu.ports_loop st s v high d port ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.ports_loop
  apply loop.spec_decr_nat (measure := fun y => 65536 - y.2.val)
    (inv := fun y => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, p⟩ h1
    simp only
    unfold vcpu.ports_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i _ hp
    have hp' : p.val < 65536 := by simpa using hp
    simp only [lift, bind_ok]
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hk8 : i2.val < 8192 ∧ i2.val % 8 = 0 := by
      have : i1.val = p.val >>> 6 := by simpa using hi1
      rw [hi2, this, Nat.shiftRight_eq_div_pow]; omega
    have ho : (core.num.U64.wrapping_add vcpu.IO i2).val < 2 ^ 15 := by rw [io_off hk8.1]; omega
    have ho8 : (core.num.U64.wrapping_add vcpu.IO i2).val % 8 = 0 := by rw [io_off hk8.1]; omega
    have ea : core.num.U64.wrapping_add (core.num.U64.wrapping_add v vcpu.IO) i2 =
        core.num.U64.wrapping_add v (core.num.U64.wrapping_add vcpu.IO i2) := ioW_eq v i2 hk8.1
    step as ⟨bit, _⟩
    refine WP.spec_bind (LawfulStore.read_spec s1 _) fun old _ => ?_
    split
    · try simp only [lift, bind_ok]
      refine WP.spec_bind (LawfulStore.write_spec s1 _ _) fun s2 e2 => ?_
      subst e2
      step as ⟨p1, hp1⟩
      rw [ea]
      exact ⟨h1.vword hH hv ho ho8, by omega⟩
    · try simp only [lift, bind_ok]
      refine WP.spec_bind (LawfulStore.write_spec s1 _ _) fun s2 e2 => ?_
      subst e2
      step as ⟨p1, hp1⟩
      rw [ea]
      exact ⟨h1.vword hH hv ho ho8, by omega⟩
  · exact h

set_option hygiene false in
/-- An error leaf at the stall's state. -/
local macro "verr" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post c1)
  | (simp only [error.truncated, error.illegal, error.invalid_arg, error.range, error.sys, bind_ok]
     exact (WP.spec_ok _).2 (Cur0.post c1)))

set_option hygiene false in
/-- The decode's prefix: the VCPU's stall, the caller, the arch and the two arguments. -/
local macro "vpre" : tactic => `(tactic| (
  unfold vcpu.decode
  refine WP.spec_bind (WP.spec_and (vcpu.stall.cur0 hA a v c0) (vcpu.stall.node hA a v c0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨c1, k1, -⟩, w1⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  refine WP.spec_bind (hA.virtualization a1) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_mono (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun _ _ => trivial
    · exact (WP.spec_ok _).2 trivial) fun f _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_mono (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun _ _ => trivial
    · exact (WP.spec_ok _).2 trivial) fun value _ => ?_
  simp (config := { decide := true }) only [fl4_abi.label.X86VCPUSetTCB, fl4_abi.label.X86VCPUWriteRegisters,
    fl4_abi.label.X86VCPUFlushTLB, fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteVMCS,
    fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUReadMSR,
    fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUDisableIOPort,
    ite_true, ite_false, if_true, if_false]))

/-- **`X86VCPUFlushTLB`.** -/
theorem vcpu.decode.flush {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hH : HeapOK H) {s : S} {a : A}
    {len v buf : U64} {call : Bool} {ex : Aeneas.Std.Array obj.Slot 3#usize} (hv : H v = some (.other 15))
    (c0 : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUFlushTLB len v call buf ex ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  vpre
  -- the flush clears the VCPU's `SVM_CPU` word (forces a full VMCB reload), then restarts
  refine WP.spec_bind (vcpu.set.cur0k hH hv (by simp [vcpu.SVM_CPU]) (by simp [vcpu.SVM_CPU]) c1)
    fun s2 ⟨c2, _⟩ => ?_
  exact restart_leaf c2 (ect.trans (c1.curW_eq.trans c2.curW_eq.symm))


/-- **`X86VCPUWriteRegisters`.** -/
theorem vcpu.decode.wregs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hH : HeapOK H) {s : S} {a : A}
    {len v buf : U64} {call : Bool} {ex : Aeneas.Std.Array obj.Slot 3#usize} (hv : H v = some (.other 15))
    (c0 : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteRegisters len v call buf ex ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  vpre
  split
  · simp only [error.truncated, bind_ok]; exact err_leaf c1 (by simp)
  refine WP.spec_bind (vcpu.decode_loop0.cur0 hH hv c1) fun s2 h2 => ?_
  refine WP.spec_bind (Pₘ := fun s3 => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s3) ?_
    fun s3 h3 => restart_leaf h3 (ect.trans (c1.curW_eq.trans h3.curW_eq.symm))
  split
  · refine WP.spec_bind (vcpu.get.any _ _ _) fun val _ => ?_
    refine WP.spec_bind (vcpu.svm.RAX.spec) fun o eo => ?_
    subst eo
    exact vcpu.set.cur0 hH hv (by simp) (by simp) h2
  · exact (WP.spec_ok _).2 h2


set_option maxHeartbeats 4000000 in
/-- **`X86VCPUSetTCB`.** -/
theorem vcpu.decode.settcb {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) {s : S} (P : VcpuPl st H Cs Rp Scs Nt Z s) {a : A}
    {len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize} (hv : H v = some (.other 15))
    (D : DecPre st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac s (.Vcpu v) extra) (he : EntAt st P3Ok s) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUSetTCB len v call buf extra ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  have c0 := Cur0.ofPre D
  vpre
  refine WP.spec_bind (idx_mem extra 0#usize (by simp)) fun x hx => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · simp only [error.truncated, bind_ok]; exact err_leaf c1 (by simp)
  rename_i hx0
  refine WP.spec_bind (D.extra s1 w1 x hx (by simpa using hx0)) fun c hc => ?_
  have hU1 : UserOK st H.tcbs Cs H.omega H U s1 := D.user.ksb k1
  cases c
  case Thread ptr =>
    have hp : ptr ∈ H.tcbs := hc.2.1 ptr rfl
    refine WP.spec_bind (smp.remote_tcb_stall.cur0 hA a1 ptr c1) ?_
    rintro ⟨s3, a2⟩ ⟨c3, k3, -⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (vcpu.detach.cur0 hA E P c3 he (hU1.ksb k3) hp) ?_
    rintro ⟨s4, a3⟩ ⟨c4, k4⟩
    try simp only [uncurry_apply_pair]
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s4 _) fun i1 ei1 => ?_
    refine WP.spec_bind (obj.Tcb.is_null.spec i1) fun b1 eb1 => ?_
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r.1) ?_ ?_
    · split
      · exact (WP.spec_ok _).2 c4
      · rename_i hb
        obtain ⟨Ac4, hX4⟩ := c4.bxi
        have hi1 : i1 ∈ H.tcbs := by
          rcases P.tcb Ac4 s4 v c4.fr hX4 hv with h0 | h1
          · rw [← ei1] at h0; subst h0; simp at eb1; exact absurd eb1 hb
          · rw [ei1]; exact h1
        exact WP.spec_mono (vcpu.detach.cur0 hA E P c4 he ((hU1.ksb k3).ksb k4) hi1) fun r ⟨c, _⟩ => c
    rintro ⟨s5, a4⟩ c5
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (vcpu.set.cur0 P.heap hv (o := vcpu.TCB) (x := ptr) (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
      c5) fun s6 c6 => ?_
    step as ⟨o, eo⟩
    subst eo
    try simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.write_spec s6 _ _) fun s7 e7 => ?_
    subst e7
    have c7 := c6.tvcpu (v := v) hp
    exact restart_leaf c7 (ect.trans (c1.curW_eq.trans c7.curW_eq.symm))
  all_goals (simp only [error.illegal, bind_ok]; exact err_leaf c1 (by simp))


set_option maxHeartbeats 4000000 in
/-- **`X86VCPUReadVMCS`** and **`X86VCPUWriteVMCS`** (VMX). -/
theorem vcpu.decode.vmcs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) (hH : HeapOK H) {s : S} {a : A}
    {lbl len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize} (hv : H v = some (.other 15))
    (D : DecPre st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac s (.Vcpu v) extra) (he : EntAt st P3Ok s)
    (hl : lbl = fl4_abi.label.X86VCPUReadVMCS ∨ lbl = fl4_abi.label.X86VCPUWriteVMCS) :
    vcpu.decode st ar s a lbl len v call buf extra ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  have c0 := Cur0.ofPre D
  rcases hl with rfl | rfl
  all_goals
    vpre
    have hU1 : UserOK st H.tcbs Cs H.omega H U s1 := D.user.ksb k1
    split
    · verr
    try simp only [bind_ok]
    split
    · verr
  · -- read
    try simp only [lift, bind_ok]
    refine WP.spec_bind (P0.vcpu.contains.p0 _ _) fun b _ => ?_
    split
    · refine WP.spec_bind (Pₘ := fun _ => True) (by
        repeat' (first
          | exact (WP.spec_ok _).2 trivial
          | refine WP.spec_bind (hA.vcpu_capability _ _) fun _ _ => ?_
          | split
          | (step as ⟨_, _⟩))) fun sup _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by
        split
        · exact vcpu.read_vmcs.any _ _ _
        · exact (WP.spec_ok _).2 trivial) fun val _ => ?_
      exact reply_leaf E he c1 hU1
    · verr
  · -- write
    refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
    rcases r with val | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (vcpu.write_vmcs.cur0 hH hv c1) fun s2 ⟨c2, k2⟩ => ?_
      exact reply_leaf E he c2 (hU1.ksb k2)
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      verr


set_option maxHeartbeats 8000000 in
/-- **`X86VCPUReadVMCB`** and **`X86VCPUWriteVMCB`** (SVM). -/
theorem vcpu.decode.vmcb {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) (hH : HeapOK H) {s : S} {a : A}
    {lbl len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize} (hv : H v = some (.other 15))
    (D : DecPre st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac s (.Vcpu v) extra) (he : EntAt st P3Ok s)
    (hl : lbl = fl4_abi.label.X86VCPUReadVMCB ∨ lbl = fl4_abi.label.X86VCPUWriteVMCB) :
    vcpu.decode st ar s a lbl len v call buf extra ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have c0 := Cur0.ofPre D
  rcases hl with rfl | rfl
  all_goals
    vpre
    have hU1 : UserOK st H.tcbs Cs H.omega H U s1 := D.user.ksb k1
    split
    swap
    · verr
    split
    · verr
  · -- read
    obtain ⟨Ac1, hX⟩ := c1.bxi
    obtain ⟨Q, R, x1'⟩ := BXI.xs hX hU1
    have x1 := XSV.start x1'
    have hct : L.curW s1 ∈ H.tcbs := hX.1.choose_spec.choose_spec.curT
    subst ect
    simp only [lift, bind_ok]
    split
    · verr
    refine WP.spec_bind (vcpu.svm.END.spec) fun e2 ee2 => ?_
    split
    · verr
    split
    · verr
    split
    · verr
    rename_i hv64
    have hval : value.val ≤ 64 := by simpa using hv64
    step as ⟨i3, _⟩
    step as ⟨i4, _⟩
    split
    · verr
    split
    · refine WP.spec_bind (E.buf _ _ _ _ s1 _ ⟨s, he, c1.fr⟩ x1.1.1 hct) fun b hb => ?_
      refine WP.spec_bind (vcpu.decode_loop1.xs hval x1 hct hb) ?_
      rintro ⟨s2, n⟩ x2
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (obj.Tcb.set_reg.xsv (v := 0#u64) x2 hct (by simp [layout.reg.BADGE, layout.reg.RDI]))
        fun s3 x3 => ?_
      refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
      refine WP.spec_bind (Pₘ := fun s4 => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s1 s4) ?_
        fun s4 x4 => running_leaf c1 x4 rfl
      unfold msg.set_msg_info
      exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
        obj.Tcb.set_reg.xsv (v := w) x3 hct (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
    · exact running_leaf c1 x1 rfl
  · -- write
    refine WP.spec_bind (vcpu.svm.END.spec) fun e2 ee2 => ?_
    refine WP.spec_bind (Pₘ := fun _ => True) (by
      split
      · simp only [lift, bind_ok]
        split
        · exact vcpu.get.any _ _ _
        · exact (WP.spec_ok _).2 trivial
      · exact (WP.spec_ok _).2 trivial) fun old _ => ?_
    by_cases hf : f.val < 2048 ∧ f.val % 8 = 0
    · refine WP.spec_bind (P0.vcpu.sanitize_vmcb.p0 _ _ _ _ _ hA) fun r _ => ?_
      rcases r with val | e
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        refine WP.spec_bind (vcpu.set.cur0k hH hv (o := f) (x := val) (by omega) hf.2 c1) fun s2 ⟨c2, k2⟩ => ?_
        -- a write to a clean-bit-tracked field clears `SVM_CPU` (forces a VMCB reload)
        refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
        refine WP.spec_bind (Pₘ := fun s3 => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s3 ∧
            L.ksb s3 = L.ksb s1) (by
          split
          · exact WP.spec_mono (vcpu.set.cur0k hH hv (by simp [vcpu.SVM_CPU]) (by simp [vcpu.SVM_CPU]) c2)
              fun s3 ⟨c3, k3⟩ => ⟨c3, k3.trans k2⟩
          · exact (WP.spec_ok _).2 ⟨c2, k2⟩) fun s2' ⟨c2', k2'⟩ => ?_
        refine WP.spec_bind (vcpu.svm.RAX.spec) fun _ _ => ?_
        refine WP.spec_bind (Pₘ := fun s3 => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s3 ∧
            L.ksb s3 = L.ksb s1) ?_ fun s3 ⟨c3, k3⟩ => reply_leaf E he c3 (hU1.ksb k3)
        split
        · exact WP.spec_mono (vcpu.set.cur0k hH hv (by simp [vcpu.REGS]) (by simp [vcpu.REGS]) c2')
            fun s3 ⟨c3, k3⟩ => ⟨c3, k3.trans k2'⟩
        · exact (WP.spec_ok _).2 ⟨c2', k2'⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_tc_ok]
        verr
    · refine WP.spec_bind (vcpu.sanitize_vmcb.off a1 f old value hf) ?_
      rintro r ⟨e, rfl⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      verr


set_option maxHeartbeats 8000000 in
/-- **`X86VCPUReadMSR`** and **`X86VCPUWriteMSR`.** -/
theorem vcpu.decode.msr {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) (hH : HeapOK H) {s : S} {a : A}
    {lbl len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize} (hv : H v = some (.other 15))
    (D : DecPre st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac s (.Vcpu v) extra) (he : EntAt st P3Ok s)
    (hl : lbl = fl4_abi.label.X86VCPUReadMSR ∨ lbl = fl4_abi.label.X86VCPUWriteMSR) :
    vcpu.decode st ar s a lbl len v call buf extra ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  have c0 := Cur0.ofPre D
  rcases hl with rfl | rfl
  all_goals
    vpre
    have hU1 : UserOK st H.tcbs Cs H.omega H U s1 := D.user.ksb k1
    repeat' (first
      | verr
      | exact reply_leaf E he c1 hU1
      | exact read_rleaf E he c1 hU1
      | exact msr_wleaf E hH hv ‹_› he c1 hU1
      | (refine WP.spec_bind (vcpu.msr_addr.off v f _) ?_
         rintro (_ | x) ho <;> try have hx := ho x rfl)
      | refine WP.spec_bind (hA.vcpu_capability _ _) fun _ _ => ?_
      | refine WP.spec_bind (P0.vcpu.canonical.p0 _ _) fun _ _ => ?_
      | refine WP.spec_bind (P0.vcpu.valid_xcr0.p0 _ _) fun _ _ => ?_
      | (simp only [bind_ok])
      | split)


set_option maxHeartbeats 8000000 in
/-- **`X86VCPUEnableIOPort`** and **`X86VCPUDisableIOPort`** (VMX). -/
theorem vcpu.decode.ioport {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S}
    (P : VcpuPl st H Cs Rp Scs Nt Z s) {a : A} {lbl len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hv : H v = some (.other 15))
    (D : DecPre st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac s (.Vcpu v) extra) (he : EntAt st P3Ok s)
    (hxs : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapSlotW H.tcbs H.omega H.frame sl)
    (hl : lbl = fl4_abi.label.X86VCPUEnableIOPort ∨ lbl = fl4_abi.label.X86VCPUDisableIOPort) :
    vcpu.decode st ar s a lbl len v call buf extra ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  have c0 := Cur0.ofPre D
  have IP := P.ioPl
  rcases hl with rfl | rfl
  all_goals
    vpre
    split
    · verr
    split
    · verr
    simp only [lift, bind_ok]
    split
    · verr
  · -- enable
    have hl0 : (0#usize : Usize).val < extra.val.length := by rw [extra.property]; simp
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun x ex => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · verr
    rename_i hx0
    have hxm : x ∈ extra.val := by rw [ex]; exact List.getElem_mem _
    refine WP.spec_bind (D.extra s1 w1 x hxm (by simpa using hx0)) fun c _ => ?_
    cases c
    case IoPort first last prior =>
      dsimp only
      split
      · verr
      split
      · verr
      refine WP.spec_bind (obj.ks_get.spec s1 _) fun old eold => ?_
      have hold : old = 0#u64 ∨ VListed st s1 old := by
        by_cases z : old = 0#u64
        · exact Or.inl z
        · right
          have e' : old = L.mem s1 (vHeadA st s1) := eold
          rw [e']; exact VListed.head (e' ▸ z)
      refine WP.spec_bind (vcpu.decode_loop3.cur0 hA IP c1 hold) ?_
      rintro ⟨s3, a2⟩ c3
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun x' ex' => ?_
      have exx : x' = x := ex'.trans ex.symm
      subst exx
      have hsw := hxs x' hxm (by simpa using hx0)
      refine WP.spec_bind (obj.Slot.set_cap.capw (s := s3) ⟨hsw.1, hsw.2⟩) fun s5 w5 => ?_
      have c3' : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s3 := c3
      have c5 := Cur0.capw c3' w5 fun b hb => hb
      unfold vcpu.ports
      refine WP.spec_bind (vcpu.ports_loop.cur0v P.heap hv c5) fun s6 c6 => ?_
      exact restart_leaf c6 (ect.trans (c1.curW_eq.trans c6.curW_eq.symm))
    all_goals verr
  · -- disable
    unfold vcpu.ports
    refine WP.spec_bind (vcpu.ports_loop.cur0v P.heap hv c1) fun s2 c2 => ?_
    exact restart_leaf c2 (ect.trans (c1.curW_eq.trans c2.curW_eq.symm))


/-- Any other label: illegal. -/
theorem vcpu.decode.other {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {lbl len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (c0 : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s s)
    (h1 : lbl ≠ fl4_abi.label.X86VCPUSetTCB) (h2 : lbl ≠ fl4_abi.label.X86VCPUWriteRegisters)
    (h3 : lbl ≠ fl4_abi.label.X86VCPUFlushTLB) (h4 : lbl ≠ fl4_abi.label.X86VCPUReadVMCS)
    (h5 : lbl ≠ fl4_abi.label.X86VCPUWriteVMCS) (h6 : lbl ≠ fl4_abi.label.X86VCPUReadVMCB)
    (h7 : lbl ≠ fl4_abi.label.X86VCPUWriteVMCB) (h8 : lbl ≠ fl4_abi.label.X86VCPUReadMSR)
    (h9 : lbl ≠ fl4_abi.label.X86VCPUWriteMSR) (h10 : lbl ≠ fl4_abi.label.X86VCPUEnableIOPort)
    (h11 : lbl ≠ fl4_abi.label.X86VCPUDisableIOPort) :
    vcpu.decode st ar s a lbl len v call buf extra ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  unfold vcpu.decode
  refine WP.spec_bind (vcpu.stall.cur0 hA a v c0) ?_
  rintro ⟨s1, a1⟩ ⟨c1, k1, -⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  refine WP.spec_bind (hA.virtualization a1) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_mono (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun _ _ => trivial
    · exact (WP.spec_ok _).2 trivial) fun f _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_mono (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun _ _ => trivial
    · exact (WP.spec_ok _).2 trivial) fun value _ => ?_
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, if_false, ite_false]
  verr

/-- **The VCPU objects' placement for the decode** (P3's): the set tuple is
the heap's, the VCPU objects' placement (`VcpuPl`), and an invoked VCPU cap
names a VCPU object. -/
structure VcpuPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  sets : T = H.tcbs ∧ Ω = H.omega ∧ Sg = H.frame
  pl : ∀ s0, EntAt st P3Ok s0 → VcpuPl st H Cs Rp Scs Nt Z s0
  cap : ∀ (Ac : Set U64) (s : S) (v : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu v) extra → H v = some (.other 15)

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

set_option maxHeartbeats 4000000 in
/-- **InvGaps' `vcpu` family**, from the VCPU objects' placement, the
transfer's buffer placement and the extra caps' slots (`IrqPlace.extra`). -/
theorem decGap_vcpu {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : VcpuPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (IPx : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
      EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapSlotW T Ω Sg sl) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu := by
  obtain ⟨eT, eΩ, eSg⟩ := P.sets
  subst eT eΩ eSg
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i v
  have hv := P.cap Ac s v extra hE D
  have hxs := IPx Ac s _ extra hE D
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  by_cases l1 : lbl = fl4_abi.label.X86VCPUSetTCB
  · subst l1; exact vcpu.decode.settcb hA E (P.pl s hE) hv D hE
  by_cases l2 : lbl = fl4_abi.label.X86VCPUWriteRegisters
  · subst l2; exact vcpu.decode.wregs hA (P.pl s hE).heap hv (Cur0.ofPre D)
  by_cases l3 : lbl = fl4_abi.label.X86VCPUFlushTLB
  · subst l3; exact vcpu.decode.flush hA (P.pl s hE).heap hv (Cur0.ofPre D)
  by_cases l4 : lbl = fl4_abi.label.X86VCPUReadVMCS
  · exact vcpu.decode.vmcs hA E (P.pl s hE).heap hv D hE (Or.inl l4)
  by_cases l5 : lbl = fl4_abi.label.X86VCPUWriteVMCS
  · exact vcpu.decode.vmcs hA E (P.pl s hE).heap hv D hE (Or.inr l5)
  by_cases l6 : lbl = fl4_abi.label.X86VCPUReadVMCB
  · exact vcpu.decode.vmcb hA E (P.pl s hE).heap hv D hE (Or.inl l6)
  by_cases l7 : lbl = fl4_abi.label.X86VCPUWriteVMCB
  · exact vcpu.decode.vmcb hA E (P.pl s hE).heap hv D hE (Or.inr l7)
  by_cases l8 : lbl = fl4_abi.label.X86VCPUReadMSR
  · exact vcpu.decode.msr hA E (P.pl s hE).heap hv D hE (Or.inl l8)
  by_cases l9 : lbl = fl4_abi.label.X86VCPUWriteMSR
  · exact vcpu.decode.msr hA E (P.pl s hE).heap hv D hE (Or.inr l9)
  by_cases l10 : lbl = fl4_abi.label.X86VCPUEnableIOPort
  · exact vcpu.decode.ioport hA (P.pl s hE) hv D hE hxs (Or.inl l10)
  by_cases l11 : lbl = fl4_abi.label.X86VCPUDisableIOPort
  · exact vcpu.decode.ioport hA (P.pl s hE) hv D hE hxs (Or.inr l11)
  exact vcpu.decode.other hA (Cur0.ofPre D) l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11


/-- The VCPU list's placement, for the I/O-port caps' finalisation. -/
theorem VcpuPlace.ioPl (P : VcpuPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    IoPortPlace st T Cs Ω H Sg Rp Scs Nt Z P3Ok := by
  obtain ⟨eT, eΩ, eSg⟩ := P.sets
  subst eT eΩ eSg
  exact fun s0 hE => (P.pl s0 hE).ioPl

end

end Fl4Proofs.P1
