/-
P3 (DESIGN.md §9), invariant line G1 (vih3): **`ValidIrqMasks ∧
ValidIrqHandlers` across the whole kernel entry** (spec side only; outside the
`JAtZ` cone).

* The decode's carry (l4v: the caps of `decode_invocation`'s result are
  `cte_wp_at`/`valid_cap` facts at the perform): `InvCAd is inv` — the caps a
  CNode invocation writes and the set-handler notification cap are `CA`.
  `okd_decodeCnode` (the copied / minted / moved / rotated caps are read from
  slots by `get_cap`, then `mask_cap` / `update_cap_data` / `derive_cap`, which
  map a handler cap only from the same handler cap), `okd_decodeIrqHandler`
  (the set-handler cap is a notification cap), `okd_fl4Decode`. The ack's
  handler cap: vih2's `okAck_fl4Decode` with the invoked cap's slot
  (`okCap_lookupCapAndSlot`), both carried to the perform by the frames.
* `vi_fl4Perform`: every perform keeps `VI` from `InvCAd` and the ack's `HIrq`.
* The shell `vi_handleInvocationR` (invC's `dpe_handleInvocationR`), the
  syscalls, every event, `fl4CallKernel`, the syscall entry.
* **`kentry_validIrqMasks`** / **`kirq_validIrqMasks`**: `ValidIrqMasks ∧
  ValidIrqHandlers` across `fl4KernelEntrySyscall true c` / `fl4CallKernel
  true .interrupt` with no side condition; `kentry_vih` / `kirq_vih`
  (ValidIrqHandlers alone needs ValidIrqMasks only through the joint
  statement: it is proved jointly).
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlersG
open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The decode's carry -/

theorem ca_maskCap {c : Cap} {is : Irq → IrqState} (h : CA c is) (r : CapRights) : CA (maskCap r c) is := by
  intro irq e; apply h irq
  cases c <;> simp_all [maskCap, capRightsUpdate]

theorem ca_updateCapData {c : Cap} {is : Irq → IrqState} (h : CA c is) (p : Bool) (w : Data) :
    CA (updateCapData p w c) is := by
  intro irq e; apply h irq
  unfold updateCapData at e
  split_ifs at e <;> first
    | (cases c <;> simp_all [badgeUpdate]; done)
    | (cases e; done)
    | (simp only [archUpdateCapData] at e; cases e)
    | (cases c <;> simp_all; done)
    | (dsimp only at e; split_ifs at e <;> cases e)
    | exact e

theorem okv_getCap {σ0 : State Unit} (hv : ValidIrqHandlers σ0) (sl : CslotPtr) :
    OkV σ0 (fun c => CA c σ0.interruptStates) (NonDetE.liftE (ε := SyscallError) (getCap (Z := Unit) sl)) := by
  intro s hs a s' h
  obtain ⟨y, hy, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨o, r⟩ := sl
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  rw [e1]
  refine ⟨hs, ?_⟩
  have := ca_of_slot (vih_of_hV hs hv) e2
  rw [hV_is hs] at this; exact this

theorem okv_returnOk_bind {ε α β : Type} {σ0 : State Unit} {Pr : β → Prop} {a : α}
    {g : α → NonDetE (State Unit) ε β} (h : OkV σ0 Pr (g a)) : OkV σ0 Pr (NonDetE.returnOk a >>= g) :=
  fun s hs => okdAt_returnOk_bind (h s hs)

theorem okv_ite_app {ε γ α : Type} {σ0 : State Unit} {Pr : α → Prop} {f g : γ → NonDetE (State Unit) ε α} {x : γ}
    (c : Prop) [Decidable c] (h1 : OkV σ0 Pr (f x)) (h2 : OkV σ0 Pr (g x)) :
    OkV σ0 Pr ((if c then f else g) x) := by
  split <;> assumption

macro "okv_step" : tactic => `(tactic| first
  | exact okv_throw _
  | exact okv_returnOk trivial
  | (refine okv_returnOk_bind ?_)
  | (refine okv_bind (okv_getCap (by assumption) _) fun _ _ => ?_)
  | (refine okv_bind (okv_frame fun v => by hv_auto) fun _ _ => ?_)
  | (apply okv_ite)
  | split)

set_option maxHeartbeats 4000000 in
theorem okv_decodeCnode {σ0 : State Unit} (hv : ValidIrqHandlers σ0) (label : Data) (args : List Data) (cap : Cap)
    (excaps : List Cap) :
    OkV σ0 (fun i => CnCA i σ0.interruptStates) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation
  repeat' (first
    | (refine okv_bind (okv_getCap hv _) fun c0 hc0 => ?_)
    | (refine okv_bind (okv_ite_app _ (okv_returnOk ?_) (okv_deriveCap _ _ ?_)) fun c1 hc1 => ?_)
    | exact okv_returnOk (by split <;> (simp only [CnCA]; assumption))
    | exact okv_returnOk ⟨ca_updateCapData (by assumption) _ _, ca_updateCapData (by assumption) _ _⟩
    | okv_step)
  all_goals first
    | (split <;> exact ca_updateCapData (ca_maskCap (by assumption) _) _ _)
    | exact ca_updateCapData (ca_maskCap (by assumption) _) _ _
    | exact ca_maskCap (by assumption) _

/-- The caps a decoded invocation will write are `CA`. -/
def InvCAd (is : Irq → IrqState) : Fl4Invocation → Prop
  | .invokeCNode i => CnCA i is
  | .invokeIRQHandler (.setIRQHandler _ c _) => CA c is
  | _ => True

theorem okd_decodeCnode (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) (s : State Unit) :
    OkDAt s (fun s' i => ValidIrqHandlers s' → InvCAd s'.interruptStates (.invokeCNode i))
      (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  intro a s' h hv'
  have e : hV s' = hV s := hv_decodeCnodeInvocation (P := fun x => hV x = hV s) _ _ _ _ s rfl _ h
  have hv : ValidIrqHandlers s := vih_of_hV e.symm hv'
  obtain ⟨-, hc⟩ := okv_decodeCnode hv label args cap excaps s rfl a s' h
  show CnCA a s'.interruptStates
  rw [hV_is e]; exact hc

theorem okd_decodeIrqHandler (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) (s : State Unit) :
    OkDAt s (fun s' v => ValidIrqHandlers s' → InvCAd s'.interruptStates (.invokeIRQHandler v))
      (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun _ => trivial)
    | exact okdAt_returnOk (fun _ => ca_noH (fun irq e => by simp_all [isNtfnCap]) _)
    | split)

set_option maxHeartbeats 4000000 in
theorem okd_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun s' inv => ValidIrqHandlers s' → InvCAd s'.interruptStates inv)
      (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun _ => trivial)
    | exact okdAt_liftME (okd_decodeCnode _ _ _ _ _)
    | exact okdAt_liftME (okd_decodeIrqHandler _ _ _ _)
    | exact okdAt_liftME (fun _ _ _ _ => trivial)
    | (apply okdAt_ite)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | split)

/-! ## The performs -/

set_option maxHeartbeats 8000000 in
theorem vi_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (h : VI σ)
    (hc : InvCAd σ.interruptStates inv) (hack : ∀ i, inv = .invokeIRQHandler (.aCKIrq i) → HIrq σ i) :
    ∀ x ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, VI x.2 := by
  cases inv with
  | invokeCNode i =>
    intro x hx
    simp only [fl4PerformInvocation] at hx
    have := (ike_bind (vh_invokeCnode i) fun _ => ike_returnOk _ :
      IKHE (ε := Unit) (VH (CnCA i)) (invokeCnode (Z := Unit) i >>= fun _ => NonDetE.returnOk [])) σ
      ⟨h.1, h.2.1, hc⟩ x hx
    exact ⟨this.1, this.2.1, trivial⟩
  | invokeIRQHandler i =>
    intro x hx
    simp only [fl4PerformInvocation] at hx
    obtain ⟨z, hz, ⟨u, hu, hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
    · obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
      have hi : IhCA i σ := by
        cases i with
        | aCKIrq irq => exact hack irq rfl
        | setIRQHandler irq c s => exact hc
        | clearIRQHandler irq => trivial
      have h1 := vi_invokeIrqHandler i σ h hi w hw
      obtain rfl := Set.mem_singleton_iff.1 hx
      exact h1
    · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  | _ => exact (show IKHE (ε := Unit) VI (fl4PerformInvocation (Z := Unit) blk call don _) from by
      simp only [fl4PerformInvocation]; hv_auto) σ h

/-! ## The invocation shell -/

theorem okCap_front (thread : ObjRef) (cptr : CapRef) (info : MessageInfo) (σ : State Unit) :
    OkDAt σ (fun s (a : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef) =>
        capOpt (s.kheap a.1.1) a.1.2 = some a.2.1)
      (do
        let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
        let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
        let extracaps ← lookupExtraCaps thread buffer info
        NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
  refine okdAt_bind fun cs s0 h0 => ?_
  obtain ⟨cap, slot⟩ := cs
  have hc := okdAt_capFault _ _ (okCap_lookupCapAndSlot _ _ _) _ _ h0
  dsimp only
  refine okdAt_bind fun buf s1 h1 => ?_
  have e1 : hV s1 = hV s0 := (ike_liftE (P := fun x => hV x = hV s0) (hv_lookupIpcBuffer false thread)) s0 rfl _ h1
  refine okdAt_bind fun exs s2 h2 => ?_
  have e2 : hV s2 = hV s1 := (hv_lookupExtraCaps (P := fun x => hV x = hV s1) _ _ _) s1 rfl _ h2
  exact okdAt_returnOk (by rw [hV_cap e2, hV_cap e1]; exact hc)

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `VI`.** -/
theorem vi_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKHE (ε := Unit) VI (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by hv_auto) fun thread => ike_bind (by hv_auto) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, VI w.2 :=
    fun w hw => (by hv_auto : IKHE (ε := Fault) VI _) σ hs w hw
  refine syscall_post' (I := VI) (Q := VI) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by hv_auto : IKH VI _) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by hv_auto : IKHE VI _) s (h1 _ has) w hw
  · intro e s hs v hv; exact (by hv_auto : IKH VI _) s hs v hv
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front thread cptr info σ _ s has
    have eE : hV s' = hV s := (by hv_auto : IKHE (fun x => hV x = hV s) _) s rfl _ hbs
    have hd : ValidIrqHandlers s' → InvCAd s'.interruptStates b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode _ _ _ _ _ _ _ _ s1) b s' hbs
    have hk : ∀ i, b = .invokeIRQHandler (.aCKIrq i) → HIrq s' i := fun i e => by
      have hc2 := okdAt_bind (fun _ s1 _ => okAck_fl4Decode _ _ _ _ _ _ _ _ s1) b s' hbs i e
      exact ⟨sl.1, sl.2, by rw [hV_cap eE, ← hc2]; exact hcap⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz' : hV z.2 = hV s' := (by hv_auto : IKHE (ε := Unit) (fun x => hV x = hV s')
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' rfl z hz
      have hz1 : VI z.2 := (by hv_auto : IKHE (ε := Unit) VI
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hd1 : InvCAd s1.interruptStates b := by rw [hV_is hz']; exact hd hI.2.1
      have hk1 : ∀ i, b = .invokeIRQHandler (.aCKIrq i) → HIrq s1 i := fun i e => hIrq_of_hV hz' (hk i e)
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := vi_fl4Perform blocking calling don b s1 hz1 hd1 hk1 _ hz2
        exact (by hv_auto : IKHE VI _) s2 hs2 y hy
      · exact vi_fl4Perform blocking calling don b s1 hz1 hd1 hk1 _ hz2
    · exact (by hv_auto : IKHE (ε := Unit) VI
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_handleInvocationR _ _ _ _ _ _)

/-! ## The kernel entry -/

set_option maxHeartbeats 8000000 in
theorem vi_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKHE (ε := Unit) VI (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_fl4HandleSyscall _ _)

set_option maxHeartbeats 8000000 in
theorem vi_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) VI (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; hv_auto

set_option maxHeartbeats 4000000 in
theorem vi_fl4HandleEvent (rep : Bool) (ev : Event) : IKHE (ε := Unit) VI (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    hv_auto
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact vi_handleEvent_other ev fun c e => h ⟨c, e⟩

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_fl4HandleEvent _ _)

set_option maxHeartbeats 4000000 in
/-- **`fl4CallKernel` keeps `VI`, for every event.** -/
theorem vi_fl4CallKernel (rep : Bool) (ev : Event) : IKH VI (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact vi_fl4CallKernel _ _)

theorem vi_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : IKH VI (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; hv_auto

/-! ## Tops -/

/-- **`ValidIrqMasks ∧ ValidIrqHandlers` across a whole syscall entry** (no side condition). -/
theorem kentry_validIrqMasks {c : Syscall} {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlers σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c σ).1), ValidIrqMasks y.2 ∧ ValidIrqHandlers y.2 :=
  fun y hy => let h := vi_fl4KernelEntrySyscall true c σ ⟨hm, hh, trivial⟩ y hy; ⟨h.1, h.2.1⟩

/-- **The same across the interrupt / timer entry** (`fl4CallKernel true .interrupt`). -/
theorem kirq_validIrqMasks {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlers σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) true .interrupt σ).1), ValidIrqMasks y.2 ∧ ValidIrqHandlers y.2 :=
  fun y hy => let h := vi_fl4CallKernel true .interrupt σ ⟨hm, hh, trivial⟩ y hy; ⟨h.1, h.2.1⟩

/-- `ValidIrqHandlers` across a syscall entry (jointly with `ValidIrqMasks`). -/
theorem kentry_vih {c : Syscall} {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlers σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c σ).1), ValidIrqHandlers y.2 :=
  fun y hy => (kentry_validIrqMasks hm hh y hy).2

theorem kirq_vih {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlers σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) true .interrupt σ).1), ValidIrqHandlers y.2 :=
  fun y hy => (kirq_validIrqMasks hm hh y hy).2

end

end Fl4Proofs.P3.SInvV
