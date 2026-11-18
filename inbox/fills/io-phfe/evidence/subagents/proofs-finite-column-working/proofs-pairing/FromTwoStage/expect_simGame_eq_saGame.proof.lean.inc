/-- The committed and derived semi-adaptive games have exactly the same laws.
[GJLS21, Definition 4.3; Wee20, §2.2, p.5]. This is expectation equality, since
independent draws occur in different syntactic orders.

**Proof sketch.** Reindex the composed tape by the finite-sum equivalence into
first-stage and second-stage tapes, using the shared coin-polynomial readers.
Commute the first-stage tape before pp/setup; its activation ignores the public
view. Unroll buildComp through its published case lemmas for one challenge and
q ordered key calls. The typed handler cases give the same state-threaded key
law as List.mapM. Convert the simulator through the toSim readers and identify
the second-stage word through viewWord_eq_viewWordBits. -/
theorem expect_simGame_eq_saGame (Sim : FEScheme.Raw.SASimulator.Raw S) (A : TwoStage)
    (q : PolyExpr) (real : Bool) (kappa : ℕ) (test : Bool → ℝ) :
    ProbComp.expect (S.simGame Sim.toSim A q real kappa) test =
      ProbComp.expect (S.saGame Sim (A.toSA (S := S) q) real kappa) test := by
  let Tape := Fin ((A.toSA (S := S) q).coins.eval kappa) → Bool
  have hlen : A.first.coinLen kappa + A.second.coinLen kappa =
      (A.toSA (S := S) q).coins.eval kappa := ?_
  swap
  · rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, TwoStage.toSA_coins, PolyExpr.eval_add]
  let e : A.first.Coins kappa × A.second.Coins kappa ≃ Tape :=
    (Fin.appendEquiv (A.first.coinLen kappa) (A.second.coinLen kappa)).trans
      (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool))
  have hword : ∀ (r1 : A.first.Coins kappa) (r2 : A.second.Coins kappa),
      List.ofFn (e (r1, r2)) = List.ofFn r1 ++ List.ofFn r2 := ?_
  swap
  · intro r1 r2
    change List.ofFn (fun i => Fin.append r1 r2 (Fin.cast hlen.symm i)) =
      List.ofFn r1 ++ List.ofFn r2
    exact (List.ofFn_congr hlen (Fin.append r1 r2)).symm.trans
      (List.ofFn_fin_append r1 r2)
  let result : Tape → ℝ := fun r => ProbComp.expect (S.pubGen kappa) fun pp =>
    if real then
      ProbComp.expect (S.setup kappa pp) fun k =>
        ProbComp.expect
          (Prod.fst <$> simulate (S.realSAImpl kappa pp k.1 k.2)
            ((A.toSA (S := S) q).run kappa pp k.1 (List.ofFn r)) none) test
    else
      ProbComp.expect (Sim.setup kappa pp) fun k =>
        ProbComp.expect
          (Prod.fst <$> simulate (S.idealSAImpl Sim kappa pp)
            ((A.toSA (S := S) q).run kappa pp k.1 (List.ofFn r)) (k.2, none)) test
  have hsa : ProbComp.expect (S.saGame Sim (A.toSA (S := S) q) real kappa) test =
      ProbComp.expect (ProbComp.sample Tape) result := ?_
  swap
  · rw [S.saGame_eq]
    cases real <;>
      simp only [Bool.false_eq_true, if_false, if_true, ProbComp.expect_bind]
    all_goals
      conv_lhs =>
        arg 2
        ext pp
        rw [ProbComp.expect_expect_sample]
      rw [ProbComp.expect_expect_sample]
      rfl
  have hsplit : ProbComp.expect (ProbComp.sample Tape) result =
      ProbComp.expect (ProbComp.sample (A.first.Coins kappa)) fun r1 =>
        ProbComp.expect (ProbComp.sample (A.second.Coins kappa)) fun r2 =>
          result (e (r1, r2)) := ?_
  swap
  · have hpair := Bridge.expect_sample_pair
      (fun p : A.first.Coins kappa × A.second.Coins kappa => result (e p))
    simp only [ProbComp.expect_bind, ProbComp.expect_pure] at hpair
    exact (ProbComp.expect_sample_equiv e result).symm.trans hpair.symm
  have hfixed : ∀ (r1 : A.first.Coins kappa) (r2 : A.second.Coins kappa),
      result (e (r1, r2)) =
        let a := Commitment.decode C q kappa (A.first.runAt kappa [] r1)
        ProbComp.expect (if real then S.realView a else S.idealView Sim.toSim a)
          (fun v => test (A.second.distinguisherL kappa v r2)) := ?_
  swap
  · intro r1 r2
    let a := Commitment.decode C q kappa (A.first.runAt kappa [] r1)
    have hb := A.coinBlocks_ofFn_append kappa r1 r2
    have hb1 : A.firstCoins kappa (List.ofFn r1 ++ List.ofFn r2) = r1 :=
      congrArg Prod.fst hb
    have hb2 : A.secondCoins kappa (List.ofFn r1 ++ List.ofFn r2) = r2 :=
      congrArg Prod.snd hb
    have hc : A.saCommitment C q kappa (List.ofFn r1 ++ List.ofFn r2) = a := ?_
    swap
    · rw [A.saCommitment_eq, hb1]
    cases real with
    | false =>
        change ProbComp.expect (S.pubGen kappa) (fun pp =>
          ProbComp.expect (Sim.setup kappa pp) (fun k =>
            ProbComp.expect
              (Prod.fst <$> simulate (S.idealSAImpl Sim kappa pp)
                ((A.toSA (S := S) q).run kappa pp k.1
                  (List.ofFn (e (r1, r2)))) (k.2, none)) test)) =
          ProbComp.expect (S.idealView Sim.toSim a)
            (fun v => test (A.second.distinguisherL kappa v r2))
        simp only [hword, TwoStage.simulate_toSA_ideal, hc, hb2, S.idealView_eq,
          FEScheme.Raw.SASimulator.Raw.toSim_setup,
          FEScheme.Raw.SASimulator.Raw.toSim_enc,
          FEScheme.Raw.SASimulator.Raw.toSim_key, Commitment.omega_eq,
          ProbComp.expect_bind, ProbComp.expect_pure]
        rfl
    | true =>
        change ProbComp.expect (S.pubGen kappa) (fun pp =>
          ProbComp.expect (S.setup kappa pp) (fun k =>
            ProbComp.expect
              (Prod.fst <$> simulate (S.realSAImpl kappa pp k.1 k.2)
                ((A.toSA (S := S) q).run kappa pp k.1
                  (List.ofFn (e (r1, r2)))) none) test)) =
          ProbComp.expect (S.realView a)
            (fun v => test (A.second.distinguisherL kappa v r2))
        simp only [hword, TwoStage.simulate_toSA_real, hc, hb2, S.realView_eq,
          ProbComp.expect_bind, ProbComp.expect_pure]
  rw [hsa, hsplit, S.simGame_eq]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure, hfixed]
  apply congrArg (ProbComp.expect (ProbComp.sample (A.first.Coins kappa)))
  funext r1
  let a := Commitment.decode C q kappa (A.first.runAt kappa [] r1)
  exact ProbComp.expect_expect_sample
    (if real then S.realView a else S.idealView Sim.toSim a)
    (A.second.Coins kappa) (fun v r2 => test (A.second.distinguisherL kappa v r2))
