set_option maxHeartbeats 4000000 in
/-- **The invoking dispatches ending in `PPQJI` under `MachPlat`**
(`dispatch_invokeJAll` with mr3's `hPre_ofZQIM`; no `PPPlat`/`IrqPlat`). -/
theorem dispatch_invokeJAllM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlobM (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hPD : JPreDecHyp (L := L) arI AR MR Z H Cs D s ar σ ct) (hR : MR ar σ.machineState)
    (hVT : ValidMachineTime σ) (hVI : ValidIrqMasks σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ := by
  rw [fl4HandleSyscall_inv hn]
  exact dispatch_invokeJM arI s ar σ J ct hct number call bl don hn hG hE hP hPD hR hVT hVI _
    fun s1 a1 σ1 h1 h2 => WP.spec_mono (hPre_ofZQIM hARI hA hnd hM hMK hPA hIA hmrt hNS hG.maxTU hG.tu s1 a1 σ1 h1 h2)
      fun _ h => h.2

variable (arI) in
/-- **The dispatch premises under `MachPlat`** (module docstring):
`KDispHyps15M` with `JEntryGlobM` for `JEntryGlob`, `JPreDecHyp` [W] beside
each invocation's path, and `ValidMachineTime` [J] at the dispatch state (l4v
`valid_machine_time`, kept by `check_budget_restart`). -/
structure KDispHyps13P (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JPreDecHyp (L := L) arI AR MR Z H Cs D s a σ ct
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp6 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JPreDecHyp (L := L) arI AR MR Z H Cs D s a σ ct
  vmt : ValidMachineTime σ

set_option maxHeartbeats 4000000 in
/-- **Every native dispatch at `J` under `MachPlat`** (`dispatch_all9M` with
`KDispHyps13P`; the mid receive leaves narrowed as `KDispHyps15M.to14M` …
`to9M`). -/
theorem dispatch_all13P [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHyps13P (L := L) arI AR MR Z H Cs D s a σ n c)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP, hPD⟩ := hK.inv _ call bl don hct hi
    exact WP.spec_mono (dispatch_invokeJAllM s a σ J _ hct n call bl don hi hG hE hP hPD hR hK.vmt hVI hARI hA hnd
      hM hMK hPA hIA hmrt hNS) fun _ h => h.toR
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hPA.minBudget a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · obtain ⟨rg, sr, cr, hm'⟩ := midSysR_of hm
    obtain ⟨hG, hE, hP, hW, hV, hS6, hPD⟩ := hK.mid _ rg sr cr hct hm'
    obtain ⟨hs, hq⟩ := J.midCQ hni hE
    have hS : JMidRecvHypS (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA _ rg)).bv) cr σ :=
      jMidRecvHypS_of hA (jMidLeavesHyp_of2 hA (jMidLeavesHyp_of3 hA (jMidLeavesHyp_of4 hA hmax htu
        (jMidLeavesHyp_of5 hA hmax htu (jMidLeavesHyp_of6 hA hmax htu hS6)))))
    exact dispatch_midJM s a σ J hni _ hct n c rg sr cr hm' hG hE hP hW.toP
      (jMidRecvHyp_of hA hG.maxTU hG.tu hs hq hW hV hS) hPD hR hK.vmt hVI hARI hA hnd hM hMK hPA hIA hmrt hNS

