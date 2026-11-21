/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq2): **`RPos` across the
syscall entry and every kernel event** (spec side only, outside the `JAtZ`
cone).

* `CfgA σ := ∀ p, CfgOK σ p`; **`cfgA_of`**: rd's `RV`, sb2's `RNE` and rd's
  `Suff` (what the front's `check_budget_restart` returning true leaves) give it.
* `CKE m`: `m` keeps `RPos` from an `RPos ∧ CfgA` state; `cke_bind_v` (a first
  step keeping `RPos` and SpecInvEqV's view `VZv`, hence `CfgA`).
* `pz_fl4Perform` (configure: SpecInvEqD's `pz_configure` with its decode fact;
  every other perform: the generated family), **`pz_handleInvocationR`** (the
  `syscall` shell `SInvU.syscall_postU` with `I s := RPos s ∧ VZv s = VZv σ`,
  the decode fact `okv_fl4DecodeCfg`), `pz_fl4HandleSyscall`,
  `pz_fl4HandleEvent_sys` (`update_time_stamp` keeps the heap, so `RV` / `RNE`;
  rd's `suff_checkBudgetRestart`), `pz_handleEvent_other`, `pz_fl4CallKernel`.
* Tops: **`kentry_rpos`**, **`kcall_rpos`** (from `RPos ∧ Rdy ∧ ScInv`, all carried).
-/
import Fl4Proofs.P3.SpecInvEqD
import Fl4Proofs.P3.SpecInvUtE
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The entry fact at every SC -/

def CfgA (σ : State Unit) : Prop := ∀ p, CfgOK σ p

theorem cfgA_vz {σ σ' : State Unit} (e : VZv σ' = VZv σ) (h : CfgA σ) : CfgA σ' := fun p => cfg_vz e (h p)

theorem cfgA_of {σ : State Unit} (hV : SInvR.RV σ) (hN : SInvB.RNE σ) (hS : SInvR.Suff σ) : CfgA σ := by
  intro p y n hk ha
  refine ⟨hN p y n hk (Or.inr ha), (hV p y n hk ha).2.1, fun hp hi => ?_⟩
  subst hp
  exact hS y n hk ha hi

theorem rv_kheap {σ σ' : State Unit} (h : SInvR.RV σ) (e : σ'.kheap = σ.kheap) : SInvR.RV σ' :=
  fun p y n hk => h p y n (by rw [← e]; exact hk)

theorem rne_kheap {σ σ' : State Unit} (h : SInvB.RNE σ) (e : σ'.kheap = σ.kheap) : SInvB.RNE σ' :=
  fun p y n hk => h p y n (by rw [← e]; exact hk)

theorem rv_vz {σ σ' : State Unit} (h : SInvR.RV σ) (e : VZv σ' = VZv σ) : SInvR.RV σ' :=
  fun p y n hk => h p y n (kheap_of_vz e hk)

theorem rne_vz {σ σ' : State Unit} (h : SInvB.RNE σ) (e : VZv σ' = VZv σ) : SInvB.RNE σ' :=
  fun p y n hk => h p y n (kheap_of_vz e hk)

/-! ## Steps from an `RPos ∧ CfgA` state -/

def CKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, RPos σ → CfgA σ → ∀ y ∈ (m.run σ).1, RPos y.2

theorem cke_of {ε α : Type} {m : NonDetE (State Unit) ε α} (h : PZKE m) : CKE m :=
  fun σ hσ _ y hy => h σ hσ y hy

theorem cke_bind_v {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : PZKE m) (hv : ∀ V, VZKE V m) (hg : ∀ a, CKE (g a)) : CKE (m >>= g) := by
  intro σ hσ hC y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm σ hσ z hz) (cfgA_vz (hv (VZv σ) σ rfl z hz) hC) y hy
  · exact hm σ hσ z hz

theorem cke_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : CKE m) (hg : ∀ a, PZKE (g a)) : CKE (m >>= g) := by
  intro σ hσ hC y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm σ hσ hC z hz) y hy
  · exact hm σ hσ hC z hz

/-- `RPos` with a fixed view. -/
def PV (V : VZw) (s : State Unit) : Prop := RPos s ∧ VZ V s

theorem pv_of {ε α : Type} {V : VZw} {m : NonDetE (State Unit) ε α} (hp : PZKE m) (hv : VZKE V m) :
    IKE (PV V) m := fun s h y hy => ⟨hp s h.1 y hy, hv s h.2 y hy⟩

/-! ## The performs -/

theorem pz_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (hσ : RPos σ) (hC : CfgA σ)
    (hD : CfgDec inv) : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, RPos y.2 := by
  intro y hy
  cases inv with
  | invokeSchedControl i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
    exact pz_configure i hD σ hσ hC x hx
  | _ => exact (show PZKE _ by simp only [fl4PerformInvocation]; pz_auto) σ hσ y hy

/-! ## The invocation shell -/

/-- **The invocation keeps `RPos`** from an `RPos ∧ CfgA` state. -/
theorem pz_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    CKE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine cke_bind_v (by pz_auto) (fun _ => by vz_auto) fun thread =>
    cke_bind_v (by pz_auto) (fun _ => by vz_auto) fun info => ?_
  intro σ hσ hC y hy
  refine syscall_postU (I := PV (VZv σ)) (Q := RPos) ?_ ?_ ?_ ?_ ?_ y hy
  · intro w hw
    refine (?_ : IKE (PV (VZv σ)) _) σ ⟨hσ, rfl⟩ w hw
    exact pv_of (by pz_auto) (by vz_auto)
  · intro f s hs v hv
    refine (?_ : PZK _) s hs.1 v hv
    pz_auto
  · intro a s has w hw
    have hs : PV (VZv σ) s := (pv_of (V := VZv σ) (by pz_auto) (by vz_auto) : IKE (PV (VZv σ)) _) σ ⟨hσ, rfl⟩ _ has
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (?_ : IKE (PV (VZv σ)) _) s hs w hw
    exact pv_of (by pz_auto) (by vz_auto)
  · intro e s hs v hv
    refine (?_ : PZK _) s hs.1 v hv
    pz_auto
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hD : CfgDec b := okv_fl4DecodeCfg (w := uV x0.2) fp info.miLabel x0.1 cptr sl cap ex buf x0.2 rfl b s' hb0
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz1 : PV (VZv σ) z.2 :=
        (pv_of (V := VZv σ) (by pz_auto) (by vz_auto) : IKE (PV (VZv σ)) (withoutPreemption (Z := Unit)
          (setThreadState thread .restart))) s' hI z hz
      have hCz : CfgA z.2 := cfgA_vz hz1.2 hC
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · have hs2 := pz_fl4Perform blocking calling don b z.2 hz1.1 hCz hD z2 hz2
        refine (?_ : PZKE _) z2.2 hs2 y hy
        pz_auto
      · exact pz_fl4Perform blocking calling don b z.2 hz1.1 hCz hD z2 hz2
    · exact (show PZKE (withoutPreemption (Z := Unit) (setThreadState thread .restart)) by pz_auto) s' hI.1 z hz

/-! ## The syscall paths and events -/

theorem pz_fl4HandleSyscall (rep : Bool) (c : Syscall) : CKE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall]
  all_goals first
    | exact cke_bind_v (by pz_auto) (fun _ => by vz_auto) fun _ => pz_handleInvocationR _ _ _ _ _ _
    | exact cke_bind_v (by pz_auto) (fun _ => by vz_auto) fun _ =>
        cke_bind (pz_handleInvocationR _ _ _ _ _ _) fun _ => by pz_auto
    | exact cke_of (by pz_auto)

/-- The syscall event from `RPos ∧ RV ∧ RNE`: the time stamp keeps the heap,
`check_budget_restart` returning true gives `Suff`, hence `CfgA`. -/
theorem pz_fl4HandleEvent_sys (rep : Bool) (c : Syscall) (σ : State Unit) (hσ : RPos σ) (hV : SInvR.RV σ)
    (hN : SInvB.RNE σ) : ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep (.syscallEvent c)).run σ).1, RPos y.2 := by
  intro y hy
  simp only [fl4HandleEvent] at hy
  obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
  · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
    clear hr
    have hk : x.2.kheap = σ.kheap := (SInvO.uts_off hx).1
    have hPx : RPos x.2 := pz_updateTimeStamp σ hσ x hx
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      unfold NonDetE.whenE at hy
      split at hy
      · rename_i ht
        obtain ⟨e2, hS⟩ := SInvR.suff_checkBudgetRestart hw ht
        rw [e2] at hy
        exact pz_fl4HandleSyscall rep c x.2 hPx (cfgA_of (rv_kheap hV hk) (rne_kheap hN hk) hS) y hy
      · rw [Set.mem_singleton_iff.1 hy]
        exact pz_checkBudgetRestart x.2 hPx w hw
    · obtain ⟨w, -, rfl⟩ := mem_liftE' hz; cases he
  · obtain ⟨x, -, rfl⟩ := mem_liftE' hz; cases he

theorem pz_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : PZKE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; pz_auto

theorem pz_fl4CallKernel (rep : Bool) (ev : Event) (σ : State Unit) (hσ : RPos σ)
    (hE : ∀ c, ev = .syscallEvent c → SInvR.RV σ ∧ SInvB.RNE σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, RPos y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 : RPos y1.2 := by
    unfold NonDetE.handleE at h1
    rw [ExceptT.run_mk] at h1
    obtain ⟨z, hz, h1⟩ := h1
    have hz' : RPos z.2 := by
      by_cases hs : ∃ c, ev = .syscallEvent c
      · obtain ⟨c, rfl⟩ := hs
        obtain ⟨hV, hN⟩ := hE c rfl
        exact pz_fl4HandleEvent_sys rep c σ hσ hV hN z hz
      · rw [fl4HandleEvent_other rep ev fun c e => hs ⟨c, e⟩] at hz
        exact pz_handleEvent_other ev (fun c e => hs ⟨c, e⟩) σ hσ z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 h1]; exact hz'
    | error e => exact (show PZKE (withoutPreemption (Z := Unit) preemptionPath) by pz_auto) s hz' y1 h1
  try dsimp only at hy
  refine (?_ : PZK _) y1.2 hb1 y hy
  pz_auto

/-! ## The tops -/

theorem vz_fl4SyscallFaultIP' {V : VZw} (t : ObjRef) : VZK V (fl4SyscallFaultIP (Z := Unit) t) := by
  unfold fl4SyscallFaultIP; exact vz_asUser _ _

/-- **`RPos` across the syscall entry**, from `RPos` and the carried `Rdy`
(rd: its `RV`) and `ScInv` (sb2: its `RNE`). -/
theorem kentry_rpos (rep : Bool) (c : Syscall) {σ : State Unit} (hP : RPos σ) (hR : SInvR.Rdy σ)
    (hS : SInvB.ScInv σ) : ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, RPos y.2 := by
  intro y ⟨y1, h1, hy⟩
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hv : VZv y2.2 = VZv σ := vz_fl4SyscallFaultIP' σ.curThread σ rfl y2 h2
  exact pz_fl4CallKernel rep _ y2.2 (pz_fl4SyscallFaultIP _ σ hP y2 h2)
    (fun _ _ => ⟨rv_vz hR.2.2.2.1 hv, rne_vz hS.2 hv⟩) y hy

/-- **`RPos` across every kernel event.** -/
theorem kcall_rpos (rep : Bool) (ev : Event) {σ : State Unit} (hP : RPos σ) (hR : SInvR.Rdy σ)
    (hS : SInvB.ScInv σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, RPos y.2 :=
  pz_fl4CallKernel rep ev σ hP fun _ _ => ⟨hR.2.2.2.1, hS.2⟩

end

end Fl4Proofs.P3.SInvE
