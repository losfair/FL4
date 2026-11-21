theorem MKD.vspace_delete_asid_pool_loop {s : S} {a : A} {base pool i : Std.U64} (h : AR a c₀) :
    vspace.delete_asid_pool_loop st arI s a base pool i ⦃ r => AR r.2 c₀ ⦄ := by
  unfold vspace.delete_asid_pool_loop
  apply loop.spec_decr_nat (measure := fun x => match x with | (_, _, x2) => 512 - x2.val)
    (inv := fun x => AR x.2.1 c₀)
  · rintro ⟨x0, x1, x2⟩ h1
    dsimp only at h1
    unfold vspace.delete_asid_pool_loop.body
    mkd_walk
  · exact h

theorem MKD.vcpu_revoke_ports_loop {s : S} {a : A} {owner low high v fuel : Std.U64} (h : AR a c₀) :
    vcpu.revoke_ports_loop st arI s a owner low high v fuel ⦃ r => AR r.2 c₀ ⦄ := by
  unfold vcpu.revoke_ports_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.2.val) (inv := fun x => AR x.2.1 c₀)
  · rintro ⟨s1, a1, v1, f1⟩ h1
    dsimp only at h1
    unfold vcpu.revoke_ports_loop.body
    mkd_walk
  · exact h

