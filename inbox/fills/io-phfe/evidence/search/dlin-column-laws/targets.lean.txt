-- SEARCH-ONLY HEADERS. No proof is supplied; native exact?/apply? probes belong to the lead.
-- Proposed home: Pairing/MatrixDH/ColumnLaws.lean, namespace TCSlib.Cryptography.Pairing.
-- Import FiniteLinear and Mathlib.Logic.Equiv.Fin.Basic; do not import Linear/Defs/SelfReduction.

/-- Left-randomized canonical real DLIN columns and uniform-base real columns have
expectation gap at most `1/N²` for every `[0,1]`-valued test, where `N` is the finite field
cardinality. This is scalar distribution glue for the column route to [Wee20, §2.1, p. 4];
the explicit loss is the probability that both canonical diagonal scalars vanish.

**Proof sketch.** The transpose of the canonical three-by-two base has a surjective
column map unless both diagonal entries vanish. Apply the existing uniform matrix-image
law through transposition, then matrix-vector associativity, on that good event. Bound
the gap by one on its complement. The published independent-coordinate and singleton
probability laws give exact exceptional mass `N⁻²`; average the pointwise gap. -/
theorem dlin_real_column_gap_le {K : Type} [Field K] [Fintype K] (rows : ℕ)
    (H : Matrix (Fin rows) (Fin 2) K → (Fin rows → K) → ℝ)
    (hH0 : ∀ M v, 0 ≤ H M v) (hH1 : ∀ M v, H M v ≤ 1) :
    let A : (Fin 2 → K) → Matrix (Fin 3) (Fin 2) K :=
      fun ab => ![![ab 0, 0], ![0, ab 1], ![1, 1]]
    |ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
            (fun L => H (L * A ab) (L *ᵥ (A ab *ᵥ rs))))) -
      ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 2) K))
        (fun M => ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => H M (M *ᵥ rs)))| ≤
      1 / (Fintype.card K : ℝ) ^ 2 := sorry

/-- Left-randomized canonical random DLIN columns and independent uniform base/response
columns have expectation gap at most `1-(1-1/N)³` for every `[0,1]`-valued test. Here `N`
is the finite field cardinality. This is scalar distribution glue for the direct canonical
column route to [Wee20, §2.1, p. 4]; the loss includes zero diagonal scalars.

**Proof sketch.** The augmented three-by-three matrix has determinant `ab(t-r-s)`.
When its three factors are nonzero, use the existing uniform matrix-image law through
transposition and split a uniform three-column output into its first two columns and last
column by standard finite-function equivalences. Bound the gap by one otherwise. Translate
the uniform scalar `t` by `-(r+s)` and apply the published independent-coordinate singleton
and complement probability laws to obtain exact exceptional mass `1-(1-1/N)³`. -/
theorem dlin_random_column_gap_le {K : Type} [Field K] [Fintype K] (rows : ℕ)
    (H : Matrix (Fin rows) (Fin 2) K → (Fin rows → K) → ℝ)
    (hH0 : ∀ M v, 0 ≤ H M v) (hH1 : ∀ M v, H M v ≤ 1) :
    let A : (Fin 2 → K) → Matrix (Fin 3) (Fin 2) K :=
      fun ab => ![![ab 0, 0], ![0, ab 1], ![1, 1]]
    |ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample K)
            (fun t => ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 3) K))
              (fun L => H (L * A ab)
                (L *ᵥ ![ab 0 * rs 0, ab 1 * rs 1, t]))))) -
      ProbComp.expect (ProbComp.sample (Matrix (Fin rows) (Fin 2) K))
        (fun M => ProbComp.expect (ProbComp.sample (Fin rows → K))
          (fun v => H M v))| ≤
      1 - (1 - 1 / (Fintype.card K : ℝ)) ^ 3 := sorry
