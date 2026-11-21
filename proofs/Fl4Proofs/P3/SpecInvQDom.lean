/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctnq1): **T4, FL4's one
domain, kept by the syscall entry and every kernel event, and at boot** (spec
side only, outside the JAtZ cone).

* `T4` (SpecInvQDomK): ScNextDom's `DomListOK` (as `DLOK`), `curDomain = 0`,
  and every TCB in domain 0. With `numDomains = 1` this is what l4v's
  `valid_queues` / `ct_in_cur_domain` domain clauses amount to: every
  `possible_switch_to` target is in the current domain (KENTRY-PLAN invC2's
  T4, the CtNQR line's first auxiliary).
* The frames: one `Q4K` lemma per spec function (SpecInvQDomF1..F5,
  generated). By hand here: the Domain invocation's writers, from the decode's
  checks (`SetDom0`: `decode_domain_set` checks `domain < numDomains = 1`;
  invC's `DomInvOK` for the schedule's start / configure), the invocation
  shell (invC's `syscall_post'`, the checks carried across `set_thread_state
  Restart` by the domain-list frame), the non-syscall events, the entries.
* The one hypothesis: `hnd : numDomains = 1` [P] (FL4's configuration;
  `JEntryGlob.nd`, invC's `kentry_domListOK`).
-/
import Fl4Proofs.P3.SpecInvQDomF5
import Fl4Proofs.P3.SpecInvDom
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom Fl4Proofs.P3.Vs

noncomputable section

set_option maxHeartbeats 1000000

theorem dlok_of {σ : State Unit} (h : DomListOK σ) : DLOK σ.domainList σ.domainStartIndex σ.domainIndex :=
  ⟨h.len, h.zero, h.start, h.startNE, h.last, h.idx, h.dom⟩

theorem domListOK_of_dlok {σ : State Unit} (h : DLOK σ.domainList σ.domainStartIndex σ.domainIndex) :
    DomListOK σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- `T4` gives invC's `DomListOK`. -/
theorem T4.domListOK {σ : State Unit} (h : T4 σ) : DomListOK σ := domListOK_of_dlok h.1

/-! ## The Domain invocation -/

/-- `set_domain` to domain 0. -/
theorem q4_setDomain0 (t : ObjRef) : Q4K (setDomain (Z := Unit) t 0) := by
  unfold setDomain threadSetDomain; q4_auto

theorem q4_domainSetStart (i : Nat) (σ : State Unit) (hi : i < σ.domainList.length)
    (hne : σ.domainList[i]? ≠ some domainEndMarker) : IKp T4 σ (domainSetStart (Z := Unit) i) := by
  unfold domainSetStart
  intro hσ x hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy1
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy2
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy3
  obtain ⟨y4, hy4, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy4
  refine q4_rescheduleRequired _ ?_ x hx
  obtain ⟨⟨hlen, hz, -, -, hlast, -, hdom⟩, hcd, hti⟩ := hσ
  exact ⟨⟨hlen, hz, hi, hne, hlast, by dsimp only; omega, hdom⟩, hcd, hti⟩

theorem q4_domainScheduleConfigure (i : Nat) (d : Domain) (dur : DomainDuration) (σ : State Unit)
    (hi : i < σ.domainList.length - 1) (hd : d = 0) (hst : i = σ.domainStartIndex → dur ≠ 0) :
    IKp T4 σ (domainScheduleConfigure (Z := Unit) i d dur) := by
  intro hσ x hx
  have h := dp_domainScheduleConfigure i d dur σ x (domListOK_of_dlok hσ.1) hi hd hst hx
  unfold domainScheduleConfigure at hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact ⟨dlok_of h, hσ.2.1, hσ.2.2⟩

/-- What `decode_domain_set` checks: the new domain is below `numDomains`, 0. -/
def SetDom0 : Fl4Invocation → Prop
  | .invokeDomain (.invokeDomainSet _ d) => d = 0
  | _ => True

theorem q4_invokeDomain (di : DomainInvocation) (σ : State Unit) (hi : DomInvOK σ (.invokeDomain di))
    (h0 : SetDom0 (.invokeDomain di)) : IKp T4 σ (invokeDomain (Z := Unit) di) := by
  cases di with
  | invokeDomainSet t d =>
    simp only [SetDom0] at h0
    subst h0
    unfold invokeDomain invokeSetDomain
    exact ikp_of_ik (ik_bind (q4_archPrepareSetDomain _ _) fun _ => q4_setDomain0 t) σ
  | invokeDomainScheduleSetStart i => exact q4_domainSetStart i σ hi.1 hi.2
  | invokeDomainScheduleConfigure i d dur => exact q4_domainScheduleConfigure i d dur σ hi.1 hi.2.1 hi.2.2

/-! ## The decode's check for SetDomain -/

theorem okdAt_and {ε α : Type} {σ : State Unit} {P P' : State Unit → α → Prop} {m : NonDetE (State Unit) ε α}
    (h : OkDAt σ P m) (h' : OkDAt σ P' m) : OkDAt σ (fun s a => P s a ∧ P' s a) m :=
  fun a s hm => ⟨h a s hm, h' a s hm⟩

theorem okq_domainSet (hnd : numDomains = 1) (args : List Data) (ex : List (Cap × CslotPtr)) (σ : State Unit) :
    OkDAt σ (fun _ d => SetDom0 (.invokeDomain d)) (decodeDomainSet (Z := Unit) args ex) := by
  unfold decodeDomainSet
  refine okdAt_bind fun a s h => ?_
  split at h
  · rename_i x xs
    have hd : a = 0 := okdAt_whenE_bind (P := fun _ (d : Domain) => d = 0) _ _ (fun hc => okdAt_returnOk (by
      rw [hnd] at hc
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth]
      have : x.toNat = 0 := by simp only [unat] at hc; omega
      rw [this]; rfl)) a s h
    subst hd
    refine okdAt_whenE_bind _ _ fun _ => ?_
    split
    · exact okdAt_returnOk (by simp [SetDom0])
    · exact okdAt_throw _
  · exact (okdAt_throw (P := fun _ (_ : Domain) => False) _ a s h).elim

theorem okq_setStart (args : List Data) (σ : State Unit) :
    OkDAt σ (fun _ d => SetDom0 (.invokeDomain d)) (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart
  refine okdAt_whenE_bind _ _ fun _ => okdAt_returnOk_bind (okdAt_gets_bind
    (okdAt_whenE_bind _ _ fun _ => okdAt_whenE_bind _ _ fun _ => okdAt_returnOk trivial))

theorem okq_configure (args : List Data) (σ : State Unit) :
    OkDAt σ (fun _ d => SetDom0 (.invokeDomain d)) (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure
  refine okdAt_whenE_bind _ _ fun _ => okdAt_returnOk_bind (okdAt_returnOk_bind (okdAt_returnOk_bind
    (okdAt_gets_bind (okdAt_whenE_bind _ _ fun _ => okdAt_whenE_bind _ _ fun _ =>
      okdAt_whenE_bind _ _ fun _ => okdAt_whenE_bind _ _ fun _ => okdAt_gets_bind
        (okdAt_whenE_bind _ _ fun _ => okdAt_returnOk trivial)))))

theorem okq_decodeDomain (hnd : numDomains = 1) (label : Data) (args : List Data) (ex : List (Cap × CslotPtr))
    (σ : State Unit) :
    OkDAt σ (fun _ d => SetDom0 (.invokeDomain d)) (decodeDomainInvocation (Z := Unit) label args ex) := by
  unfold decodeDomainInvocation
  split
  · exact okq_domainSet hnd args ex σ
  · exact okq_configure args σ
  · exact okq_setStart args σ
  · exact okdAt_throw _

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `SetDom0`.** -/
theorem okq_fl4Decode (hnd : numDomains = 1) (fp : Bool) (label : Data) (args : List Data) (ci : CapRef)
    (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (σ : State Unit) :
    OkDAt σ (fun _ inv => SetDom0 inv) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | exact okdAt_liftME (fun _ _ _ => trivial)
    | exact okdAt_liftME (okq_decodeDomain hnd _ _ _ σ)
    | (apply okdAt_ite)
    | split)

/-! ## The perform and the invocation shell -/

set_option maxHeartbeats 8000000 in
/-- Every perform but the Domain invocation's keeps `T4`. -/
theorem q4_fl4PerformND (blk call don : Bool) (inv : Fl4Invocation) (h : ∀ d, inv ≠ .invokeDomain d) :
    Q4KE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeDomain d => exact absurd rfl (h d)
  | _ => simp only [fl4PerformInvocation]; q4_auto

/-- **Every perform keeps `T4`**, from the decode's checks at its start. -/
theorem q4_perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (x : Except Unit (List Data) × State Unit) (hs : T4 σ) (hi : DomInvOK σ inv) (h0 : SetDom0 inv)
    (hx : x ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1) : T4 x.2 := by
  by_cases hd : ∃ d, inv = .invokeDomain d
  · obtain ⟨d, rfl⟩ := hd
    simp only [fl4PerformInvocation] at hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    obtain ⟨z, hz, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact q4_invokeDomain d σ hi h0 hs z hz
  · exact q4_fl4PerformND blk call don inv (fun d e => hd ⟨d, e⟩) σ hs x hx

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `T4`.** -/
theorem q4_handleInvocationR (hnd : numDomains = 1) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    Q4KE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by q4_auto) fun thread => ike_bind (by q4_auto) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, T4 w.2 :=
    fun w hw => (by q4_auto : Q4KE (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ hs w hw
  refine syscall_post' (I := T4) (Q := T4) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by q4_auto : Q4K (NonDet.when blocking (handleFault (Z := Unit) thread f))) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by q4_auto : Q4KE (do
      let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
      fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf)) s (h1 _ has) w hw
  · intro e s hs v hv
    exact (by q4_auto : Q4K (NonDet.when calling <|
      fl4ReplyFromKernelError (Z := Unit) rep thread (msgFromSyscallError e))) s hs v hv
  · intro a s b s' _ hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hd : DomInvOK s' b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode hnd _ _ _ _ _ _ _ _ s1) b s' hbs
    have h0 : SetDom0 b :=
      okdAt_bind (P := fun _ inv => SetDom0 inv) (fun _ s1 _ => okq_fl4Decode hnd _ _ _ _ _ _ _ _ s1) b s' hbs
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz' : dlV z.2 = dlV s' := (by dl_auto : DLE (withoutPreemption (Z := Unit)
        (setThreadState thread .restart))) s' z hz
      have hs1 : T4 z.2 := (by q4_auto : Q4KE (withoutPreemption (Z := Unit)
        (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hd1 : DomInvOK s1 b := domInvOK_of_dlV hz' hd
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := q4_perform blocking calling don b s1 _ hs1 hd1 h0 hz2
        exact (by q4_auto : Q4KE (withoutPreemption (Z := Unit) (do
              let state ← getThreadState thread
              match state with
              | .restart => do
                NonDet.when calling <|
                  replyFromKernel thread (0, rp)
                setThreadState thread .running
              | _ => return ()))) s2 hs2 y hy
      · exact q4_perform blocking calling don b s1 _ hs1 hd1 h0 hz2
    · exact (by q4_auto : Q4KE (withoutPreemption (Z := Unit)
        (setThreadState thread .restart))) s' hI z hz

/-! ## The kernel entry -/

macro_rules | `(tactic| q4_leaf) => `(tactic| (refine q4_handleInvocationR ?_ _ _ _ _ _ _; assumption))

set_option maxHeartbeats 8000000 in
theorem q4_fl4HandleSyscall (hnd : numDomains = 1) (rep : Bool) (c : Syscall) :
    Q4KE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> q4_auto

set_option maxHeartbeats 8000000 in
/-- The non-syscall events (no invocation). -/
theorem q4_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    Q4KE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; q4_auto

set_option maxHeartbeats 4000000 in
theorem q4_fl4HandleEvent (hnd : numDomains = 1) (rep : Bool) (ev : Event) :
    Q4KE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ike_bind (by q4_auto) fun _ => ike_bind (by q4_auto) fun _ =>
      ike_whenE _ (q4_fl4HandleSyscall hnd rep c)
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact q4_handleEvent_other ev fun c e => h ⟨c, e⟩

/-- **`fl4CallKernel` keeps `T4`, for every event.** -/
theorem q4_fl4CallKernel (hnd : numDomains = 1) (rep : Bool) (ev : Event) :
    Q4K (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ik_bind (ike_handleE (q4_fl4HandleEvent hnd rep ev) fun _ => by q4_auto) fun _ => ?_
  exact ik_bind q4_fl4Awaken fun _ => ik_bind q4_schedule fun _ => q4_activateThread

theorem q4_fl4KernelEntrySyscall (hnd : numDomains = 1) (rep : Bool) (c : Syscall) :
    Q4K (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall
  exact ik_bind (ik_gets _) fun ct => ik_bind (q4_fl4SyscallFaultIP ct) fun _ => q4_fl4CallKernel hnd rep _

/-! ## Tops -/

/-- **(b) T4 across a whole syscall entry.** `hnd : numDomains = 1` [P]
(FL4's configuration; SetDomain's and DomainScheduleConfigure's decodes check
`domain < numDomains`). -/
theorem kentry_t4 (hnd : numDomains = 1) {c : Syscall} {σ : State Unit} (h : T4 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c σ).1), T4 y.2 :=
  fun y hy => q4_fl4KernelEntrySyscall hnd true c σ h y hy

/-- **(c) T4 across every kernel event** (`fl4CallKernel rep ev`; the interrupt /
timer entry is `ev = .interrupt`). -/
theorem kcall_t4 (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : T4 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev σ).1), T4 y.2 :=
  fun y hy => q4_fl4CallKernel hnd rep ev σ h y hy

/-- **(d) T4 at boot** (`initASt`). -/
theorem boot_t4 : T4 (initASt (Z := Unit)) := by
  refine ⟨dlok_of domListOK_init, rfl, ?_⟩
  intro p x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [dom0, defaultDomain]) | simp_all [dom0]

end

end Fl4Proofs.P3.SInvQ
