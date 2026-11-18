-- SEARCH-ONLY PROPOSED TARGET. No helper proof is supplied or claimed.
-- Proposed namespace: TCSlib.Cryptography.Pairing, before namespace BilinearGen.

/-- Uniform scalar responses and responses multiplied by two independent diagonal masks
have expectation gap at most `2/N - 1/N²` for every test with values in `[0,1]`, where `N`
is the finite field's cardinality. This is fixed-field probability glue for the random-law
comparison [GJLS21, Definition 3.3, p.18; JLS26, §1.1, p.3].

**Proof sketch.** Fix the diagonal pair. If both entries are nonzero, their coordinatewise
multiplication permutations preserve the uniform response law. Otherwise each bounded
expectation lies in `[0,1]`, so its gap is at most one. Average the resulting bad-event
indicator with `abs_expect_sub_le_expect`. Reindex the two diagonal coordinates as a product
and evaluate the exact bad mass `1/N + (1-1/N)/N = 2/N - 1/N²`, using existing singleton
probability and sample/Fubini readers. No sampler is constructed. -/
theorem dlinDiagonal_random_gap_le {K : Type} [Field K] [Fintype K]
    (H : (Fin 2 → K) → (Fin 3 → K) → ℝ)
    (hH0 : ∀ ab u, 0 ≤ H ab u) (hH1 : ∀ ab u, H ab u ≤ 1) :
    |ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 3 → K)) (H ab)) -
      ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample K)
            (fun t => H ab ![ab 0 * rs 0, ab 1 * rs 1, t])))| ≤
      2 / (Fintype.card K : ℝ) - 1 / (Fintype.card K : ℝ) ^ 2 := sorry
