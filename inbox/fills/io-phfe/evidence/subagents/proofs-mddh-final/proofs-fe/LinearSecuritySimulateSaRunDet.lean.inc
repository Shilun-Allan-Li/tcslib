/-- Simulation of the typed bounded run by any deterministic handler has the shared
runDet form. This is the handler-machine hypothesis shape, without constructing a machine.

**Proof sketch.** Use `SAAdv.run_eq` and the published
`simulate_buildComp_detImpl_eq_pure`, with the same budget, history and initial state. -/
theorem simulate_saRun_det {ι' σ : Type} {spec' : OracleSpec ι'}
    (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim)
    (κ : ℕ) (pp : PublicParams G κ) (pk : MPK G ℓ zDim κ pp) (r : List Bool)
    (h : ∀ i, (saSpec G PG zDim κ pp).dom i → σ →
      (saSpec G PG zDim κ pp).rng i × σ) (s : σ) :
    simulate (detImpl (spec' := spec') h) (SAAdv.run G PG zDim A κ pp pk r) s =
      .pure (runDet (A.next κ pp pk r) false h (A.budget.eval κ) [] s) := by
  rw [SAAdv.run_eq G PG zDim A κ pp pk r]
  exact simulate_buildComp_detImpl_eq_pure (spec' := spec')
    (A.next κ pp pk r) false h (A.budget.eval κ) [] s
