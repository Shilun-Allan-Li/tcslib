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
  cases real <;>
    simp only [S.simGame_eq, S.saGame_eq, Bool.false_eq_true, if_false, if_true,
      S.realView_eq, S.idealView_eq,
      FEScheme.Raw.SASimulator.Raw.toSim_setup,
      FEScheme.Raw.SASimulator.Raw.toSim_enc,
      FEScheme.Raw.SASimulator.Raw.toSim_key,
      Commitment.omega_eq,
      ProbComp.expect_bind, ProbComp.expect_map, ProbComp.expect_pure]
  -- Two remaining branches: ideal and real, after exact-law expansion.
  -- Each needs the fixed-tape run law and the same finite coin reindexing.
  all_goals sorry
