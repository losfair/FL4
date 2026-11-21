/-
P3 (DESIGN.md §9), invariant line G1 (ft3): **`B` across
`handle_invocation` and `handle_recv`** (spec side only), from
`B [ct] [ct] [ct] (· = ct)`.

* `fl4HandleInvocationR` (`ft_syscall_post`): lookups and decode are frame;
  the post is the invariant, or, for a blocking invocation whose lookup
  faulted, `B [] [] [ct]` (`b_handleFault ct` with `E = []`); the perform
  phase starts after `set_thread_state ct Restart` (`NoRpl [ct]`).
* `handle_recv`: lookups keep the invariant; the receive itself runs with
  `ct`'s exemption ended (`ct ∈ L`), and for a notification also out of `K`
  (`ct` joins a queue); a lookup fault is `b_handleFault ct`. The post is
  `B [] [] [] (· = ct)`.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsH8
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `handle_invocation` -/

set_option maxHeartbeats 8000000 in
theorem b_fl4HandleInvocationR (ct : ObjRef) (rep calling blocking don first : Bool) (cptr : CapRef) :
    HKE (B [ct] [ct] [ct] (· = ct))
      (fun s => B [ct] [ct] [ct] (· = ct) s ∨ (blocking = true ∧ B [] [] [ct] (· = ct) s))
      (fl4HandleInvocationR (Z := Unit) rep calling blocking don first cptr) := by
  unfold fl4HandleInvocationR
  refine hke_gets_bind fun σ hσ => ?_
  have hc : σ.curThread = ct := hσ.1.2
  simp only [hc, withoutPreemption]
  refine hke_bind (R := B [ct] [ct] [ct] (· = ct))
    (Q := fun s => B [ct] [ct] [ct] (· = ct) s ∨ (blocking = true ∧ B [] [] [ct] (· = ct) s))
    (hk_liftE (hk_of_ik (b_of_gf fun F S => ?_))) (fun info => ?_) (fun s h => Or.inl h) σ hσ
  · fg_auto
  intro σ' hσ' y0 hy0
  refine ft_syscall_post (I := B [ct] [ct] [ct] (· = ct))
    (Q := fun s => B [ct] [ct] [ct] (· = ct) s ∨ (blocking = true ∧ B [] [] [ct] (· = ct) s)) ?_ ?_ ?_ ?_ ?_ y0 hy0
  · refine (b_of_gfE (L := [ct]) (E := [ct]) (K := [ct]) (C := (· = ct)) fun F S => ?_) σ' hσ'
    fg_auto
  · intro f s hs v hv
    unfold NonDet.when at hv
    split at hv
    · rename_i hb
      exact Or.inr ⟨hb, b_mono (b_handleFault (L := [ct]) (E := []) (K := [ct]) (C := (· = ct)) ct f
        (List.mem_singleton_self _) s hs v hv) (fun _ h => by simp at h) (fun _ h => h) id⟩
    · rw [Set.mem_singleton_iff.1 hv]; exact Or.inl hs
  · intro a s has w hw
    have hs : B [ct] [ct] [ct] (· = ct) s := by
      refine (b_of_gfE (L := [ct]) (E := [ct]) (K := [ct]) (C := (· = ct)) fun F S => ?_) σ' hσ' _ has
      fg_auto
    obtain ⟨sl, cap, ex, buf⟩ := a
    refine (b_of_gfE (L := [ct]) (E := [ct]) (K := [ct]) (C := (· = ct)) fun F S => ?_) s hs w hw
    fg_auto
  · intro e s hs v hv
    refine Or.inl ((b_of_gf (L := [ct]) (E := [ct]) (K := [ct]) (C := (· = ct)) fun F S => ?_) s hs v hv)
    fg_auto
  · intro a s b s' _ _ hI y hy
    refine hke_bind (R := fun s => B [ct] [ct] [ct] (· = ct) s ∧ NoRpl [ct] s)
      (Q := fun s => B [ct] [ct] [ct] (· = ct) s ∨ (blocking = true ∧ B [] [] [ct] (· = ct) s)) ?_ (fun _ => ?_)
      (fun s h => Or.inl h.1) s' hI y hy
    · refine hk_liftE fun σ1 h1 y1 hy1 => ⟨b_setThreadState ct .restart
        (Or.inr (Or.inl (List.mem_singleton_self _))) (fun _ h => h) (Or.inl fun h => h)
        (fun _ => Or.inl trivial) σ1 h1 y1 hy1, ?_⟩
      intro u hu x hx
      rw [List.mem_singleton.1 hu] at hx
      rw [sts_post hy1 x hx]; exact fun h => h
    · refine hke_bind (R := B [ct] [ct] [ct] (· = ct)) (b_fl4PerformInvocation ct _ _ _ _) (fun reply => ?_)
        (fun s h => Or.inl h)
      refine hk_post (hk_liftE (hk_of_ik ?_)) fun s h => Or.inl h
      b_autoE

/-! ## `handle_recv` -/

theorem ct_nmem_nil {ct : ObjRef} : ct ∉ ([] : List ObjRef) := fun h => by cases h

set_option maxHeartbeats 8000000 in
theorem b_handleRecv (ct : ObjRef) (blk canReply : Bool) :
    HK (B [ct] [ct] [ct] (· = ct)) (B [] [] [] (· = ct)) (handleRecv (Z := Unit) blk canReply) := by
  have hRI : ∀ s, B [ct] [ct] [ct] (· = ct) s → B [ct] [] [ct] (· = ct) s := fun s h => i0_dropE h
  have hRIP : ∀ c rc, HK (B [ct] [ct] [ct] (· = ct)) (B [] [] [] (· = ct)) (receiveIpc (Z := Unit) ct c blk rc) :=
    fun c rc s hs z hz => b_mono (b_receiveIpc (L := [ct]) (E := []) (K := [ct]) (C := (· = ct)) ct c blk rc
      (List.mem_singleton_self _) ct_nmem_nil s (hRI s hs) z hz) (fun _ h => by cases h) (fun _ h => by cases h) id
  have hRS : ∀ c, HK (B [ct] [ct] [ct] (· = ct)) (B [] [] [] (· = ct)) (receiveSignal (Z := Unit) ct c blk) :=
    fun c s hs z hz => b_mono (b_receiveSignal (L := [ct]) (E := []) (K := []) (C := (· = ct)) ct c blk
      (List.mem_singleton_self _) ct_nmem_nil ct_nmem_nil s (b_mono (hRI s hs) (fun _ h => h) (fun _ h => by cases h) id)
      z hz) (fun _ h => by cases h) (fun _ h => by cases h) id
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = ct := hσ.1.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 := (b_of_gf (fun _ _ => by fg_auto) : BK [ct] [ct] [ct] (· = ct)
    (NonDet.liftM dataToCptr (asUser (Z := Unit) ct (getRegister cap_register)))) σ hσ y2 h2
  refine hk_catch (I := B [ct] [ct] [ct] (· = ct)) ?_ (fun e => ?_) y2.2 hb2 y hy
  · (try dsimp only)
    refine hkr_bind (b_of_gfE fun F S => ?_) (fun epCap => ?_)
    · fg_auto
    (try dsimp only)
    split
    · split
      · split
        · refine hkr_bind (b_of_gfE fun F S => ?_) (fun rc => ?_)
          · fg_auto
          exact hkr_liftE (hRIP _ rc)
        · refine hkr_bind (b_of_gfE fun F S => ?_) (fun rc => ?_)
          · fg_auto
          exact hkr_liftE (hRIP _ rc)
      · exact hkr_throw _
    · split
      · refine hkr_bind (b_of_gfE fun F S => ?_) (fun bt => ?_)
        · fg_auto
        (try dsimp only)
        split
        · exact hkr_liftE (hRS _)
        · exact hkr_throw _
      · exact hkr_throw _
    · exact hkr_throw _
  · exact fun s hs z hz => q1_q0 (b_mono (b_handleFault (L := [ct]) (E := []) (K := [ct]) (C := (· = ct)) ct e
      (List.mem_singleton_self _) s hs z hz) (fun _ h => by simp at h) (fun _ h => h) id)

end

end Fl4Proofs.P3.SInv
