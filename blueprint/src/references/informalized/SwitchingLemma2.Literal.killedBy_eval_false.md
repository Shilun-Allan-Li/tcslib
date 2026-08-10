<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: Literal.killedBy_eval_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A killed literal evaluates to false under the restriction

**Claim.** Let `l : Literal n` and `ρ : Restriction n` with
`Literal.killedBy l ρ`, i.e. `ρ l.var = some l.neg`. Then for every
`x : Fin n → Bool`, `l.eval (ρ.extend x) = false`.

**Proof.**

1. `unfold Literal.killedBy at h` exposes `h : ρ l.var = some l.neg`.
2. `simp [Literal.eval, Restriction.extend, h]`: `ρ.extend x` at `l.var` is
   `(ρ l.var).getD (x l.var) = l.neg` by `h`, and `Literal.eval` returns
   `!l.neg` when `l.neg` is true and `l.neg` otherwise — `false` either way.

**Remark.** "Killed" means the restriction sets the variable to the polarity
that falsifies the literal, so the literal is dead regardless of the free
coordinates supplied by `x`.

**Used in.** `killedAll_implies_dtDepth_zero` (same file) and
`canonicalDTree_go_correct` in `Switching/CanonicalDTree.lean`, both via
`list_all_eq_false_of_mem`.
