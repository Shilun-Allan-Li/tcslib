theorem simulate_buildComp_detImpl_eq_pure
    (next : QueryLog spec → Move spec α) (timeout : α)
    (h : ∀ i, spec.dom i → σ → spec.rng i × σ)
    (q : ℕ) (hist : QueryLog spec) (s : σ) :
    simulate (detImpl (spec' := spec') h) (buildComp next timeout q hist) s =
      .pure (runDet next timeout h q hist s) := by
  induction q generalizing hist s with
  | zero =>
      -- Budget zero: a return succeeds, while a query times out without a state update.
      cases hn : next hist with
      | ret a =>
          rw [buildComp_zero_of_ret hn, runDet_zero_of_ret next timeout h hist s hn,
            simulate_pure]
      | query i x =>
          rw [buildComp_zero_of_query hn, runDet_zero_of_query next timeout h hist s hn,
            simulate_pure]
  | succ q ih =>
      -- Positive budget: only the query case threads the deterministic answer/state.
      cases hn : next hist with
      | ret a =>
          rw [buildComp_succ_of_ret hn, runDet_succ_of_ret next timeout h hist s hn,
            simulate_pure]
      | query i x =>
          rw [buildComp_succ_of_query hn, runDet_succ_of_query next timeout h hist s hn,
            simulate_query, detImpl_apply, OracleComp.pure_bind]
          exact ih (hist ++ [⟨i, x, (h i x s).1⟩]) (h i x s).2
