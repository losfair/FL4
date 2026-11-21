/-
P3 (DESIGN.md §9), IPC: **the IPC-buffer facts at a `JAtZ` state**
(handoff/glob.md gl15): `IpcBufCapOK` (`JAtZ.bok`), `BufCover` (from `bok`
and `JAtZ.fcov`, `bufCover_of_frameCover`) and `BufPlaced`
(`JAtZ.bufPlacedJ`), the three facts JEntryGlob's ∀-state premises
`ipcBufOK` / `bufCover` / `bufPlaced` gave (XTopJointFault's `XferHZ`):
`JAtZ.xferH`.
-/
import Fl4Proofs.P3.BufInv
import Fl4Proofs.P3.XTopJointData
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Cover
open Fl4Spec

/-- The words of an aligned buffer in an aligned page are 8-aligned. -/
theorem bufAddr_al8 (vms : VMPageSize) (pb tb : BitVec 64) (k : Nat) (hk : k < 128)
    (hpb : pb.toNat % 2 ^ pageBitsForSize vms = 0) (htb : tb.toNat % 1024 = 0) :
    (Endp.bufAddr (pb + (tb &&& mask (pageBitsForSize vms))) k).toNat % 8 = 0 := by
  have hm := Endp.pageBits_mem vms
  set b := pageBitsForSize vms with hbdef
  have hb : 12 ≤ b ∧ b ≤ 30 := by simp at hm; omega
  have h2b : 1024 ∣ 2 ^ b := by
    have : 2 ^ 10 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have h8 : 8 ∣ 2 ^ b := by
    have : 2 ^ 3 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have hpos : 0 < 2 ^ b := by positivity
  have hpbL := pb.isLt
  have htbL := tb.isLt
  have hoff := Endp.mask_toNat' b hm tb
  have hoff1 : tb.toNat % 2 ^ b % 1024 = 0 := by
    rw [Nat.mod_mod_of_dvd _ h2b]; exact htb
  have hpb8 : pb.toNat % 8 = 0 := by rw [← Nat.mod_mod_of_dvd _ h8, hpb]
  unfold Endp.bufAddr
  rw [BitVec.toNat_add, BitVec.toNat_add, hoff, BitVec.toNat_ofNat]
  have hk8 : k * wordSize % 2 ^ 64 = k * 8 := by
    simp only [wordSize]; omega
  rw [hk8]
  have hoff2 : tb.toNat % 2 ^ b < 2 ^ 64 := by omega
  omega

/-- **`BufCover` from `IpcBufCapOK` and `FrameCover`.** -/
theorem bufCover_of_frameCover {T : Set U64} {B : Set (U64 × Word)} {σ : State Unit}
    (hO : Endp.IpcBufCapOK σ) (hF : FrameCover B σ) : Endp.BufCover T B σ := by
  intro t _ x b q hk hq w hw i hi
  unfold Endp.ipcBufOf at hq
  split at hq
  · rename_i dev pb R mt vms md he
    split_ifs at hq with hc
    cases hq
    have hro : vmReadOnly ⊆ R := by
      rcases hc with h | ⟨h, -⟩
      · exact fun z hz => h (by unfold vmReadOnly vmReadWrite at *; simp at hz ⊢; simp [hz])
      · exact h
    obtain ⟨-, -, hd, ha, hpa⟩ := hO t.bv x hk dev pb R mt vms md he hro
    have hbv : (Endp.fl4BufA w i).bv = Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val := by
      rw [fl4BufA_bv, hw]
    have hval : (Endp.fl4BufA w i).val =
        (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val).toNat := by
      rw [← hbv]; rfl
    obtain ⟨sz, hsz⟩ := hd i.val hi
    have hn := Endp.and_not_mask_toNat (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val) _
      (Endp.pageBits_mem sz)
    have hpos : 0 < 2 ^ pageBitsForSize sz := by positivity
    have hlo := Nat.div_mul_le_self (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val).toNat
      (2 ^ pageBitsForSize sz)
    have hhi := Nat.lt_div_mul_add
      (a := (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val).toNat) hpos
    have h8 := bufAddr_al8 vms pb x.tcbIpcBuffer i.val hi hpa ha
    have hm := hF _ sz hsz (Endp.fl4BufA w i) (by rw [hn, hval]; exact hlo) (by rw [hn, hval]; exact hhi)
      (by rw [hval]; exact h8)
    rw [hbv] at hm; exact hm
  · cases hq

end Cover

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The IPC-buffer facts at a `JAtZ` state** (module docstring). -/
theorem JAtZ.xferH (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    Endp.IpcBufCapOK σ ∧ Endp.BufCover Z.T Z.B σ ∧ Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ :=
  ⟨J.bok, bufCover_of_frameCover J.bok J.fcov, J.bufPlacedJ⟩

end

end

end Fl4Proofs.P3
