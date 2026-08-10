<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: innerProduct_eq_expect_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The self inner product is the second moment

**Claim.** For `f : BooleanFunc n`, `innerProduct f f = expect (fun x => f x ^ 2)`.

**Proof.** A definitional rewrite. `unfold innerProduct expect uniformWeight`
leaves the same weight `(2⁻¹)^n` on both sides, so `congr 1` reduces to the two
sums, and termwise `Finset.sum_congr rfl` with `ring` identifies `f x * f x` with
`f x ^ 2`. ∎

**Used in.** `hypercontractivity_p_2_general`, purely to move between the two
spellings of `E₂` — the inner-product form needed by `noiseOp_self_adjoint` and
the expectation form appearing in the statement.
