# manual lemma texts; {P} = prefix, {F} = family (NSK), {FE} = family E
M={}
M["resolveAddressBits'"]='''theorem {P}_resolveAddressBits' (p : Cap × CapRef) : {FE} (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by {P}_auto)) fun nc => ?_
        split
        · exact {P}_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_resolveAddressBits' _)
'''
M['transferCapsLoop']='''theorem {P}_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      {F} (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; {P}_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => {P}_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | {P}_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_transferCapsLoop _ _ _ _ _ _)
'''
M['recDelF']=''
M['recDel']='''/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem {P}_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, {F} (f k)) (k : RecDelCall) : {FE} (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, {FE} (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; {P}_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; {P}_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> {P}_auto
    all_goals exact hrec' _

theorem {P}_recDel (c : RecDelCall) : {FE} (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => {P}_recDelF hf k) c
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_recDel _)
'''
M['capRevokeF']=''
M['capRevoke']='''/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem {P}_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, {F} (f k)) (sl : CslotPtr) : {FE} (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, {FE} (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  {P}_auto
  all_goals exact hrec' _

theorem {P}_capRevoke (sl : CslotPtr) : {FE} (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => {P}_capRevokeF hf k) sl
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_capRevoke _)
'''
M['fl4Awaken']='''theorem {P}_fl4Awaken : {F} (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact {P}_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_fl4Awaken)
'''
DEPS={'recDel':['recDelF'],'capRevoke':['capRevokeF'],'fl4Awaken':['sendSignal']}

M['getExtraCptrs']='''theorem {P}_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : {F} (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; {P}_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_getExtraCptrs _ _)
'''
M['receiveIpc']='''set_option maxHeartbeats 4000000 in
theorem {P}_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    {F} (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; {P}_auto
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_receiveIpc _ _ _ _)
'''
M['decodeTcbInvocation']='''/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem {P}_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : {FE} (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; {P}_auto
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_decodeTcbInvocation _ _ _ _ _)
'''
M['fl4DecodeTcbInvocation']='''/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem {P}_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    {FE} (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; {P}_auto
macro_rules | `(tactic| {P}_leaf) => `(tactic| with_reducible exact {P}_fl4DecodeTcbInvocation _ _ _ _ _ _)
'''
