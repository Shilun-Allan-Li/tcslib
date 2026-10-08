<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: innerProduct_eq_expect_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The self inner product is the second moment

**Claim.** For `f : BooleanFunc n`, `innerProduct f f = expect (fun x => f x ^ 2)`.

**Proof.** A definitional rewrite. `unfold innerProduct expect uniformWeight`
leaves the same weight `(2⁻¹)^n` on both sides, so `congr 1` reduces to the two
sums, and termwise `Finset.sum_congr rfl` with `ring` identifies `f x * f x` with
`f x ^ 2`. ∎

**Used in.** `BooleanAnalysis.Hypercontractivity.hypercontractivity_p_2_general` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean`.
