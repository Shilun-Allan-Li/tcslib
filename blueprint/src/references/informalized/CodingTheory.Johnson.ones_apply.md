<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: ones_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every coordinate of the all-ones vector is 1

**Claim.** For `i : Fin n`, the `i`-th coordinate of `ones : Euc n` equals
`(1 : ℝ)`. Here `Euc n = EuclideanSpace ℝ (Fin n)` and
`ones = WithLp.toLp 2 (fun _ => (1 : ℝ))`.

**Proof.** Immediate from `simp [ones]`: unfolding `ones` reduces the
coordinate projection of `WithLp.toLp` to the underlying constant function.

**Remark.** A `@[simp]` unfolding lemma whose only job is to let later
computations evaluate `ones` coordinatewise; it is the `ones` counterpart of
`pmOne_apply_true` / `pmOne_apply_false`.
