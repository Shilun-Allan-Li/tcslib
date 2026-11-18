/-- The committed simulation advantage equals the semi-adaptive advantage of its
explicit typed embedding, with no loss. [GJLS21, Definition 4.3; Wee20, §2.2].

**Proof sketch.** Apply the preceding exact law identity to each experiment's
acceptance test, then read the two advantages through their published equations. -/
theorem simAdv_eq_saSimAdv (Sim : FEScheme.Raw.SASimulator.Raw S) (A : TwoStage)
    (q : PolyExpr) (kappa : ℕ) :
    S.simAdv Sim.toSim A q kappa = S.saSimAdv Sim (A.toSA (S := S) q) kappa := by
  simp only [S.simAdv_eq, S.saSimAdv_eq, advantage_eq, accept_eq,
    ProbComp.prob_eq_expect, S.expect_simGame_eq_saGame]
