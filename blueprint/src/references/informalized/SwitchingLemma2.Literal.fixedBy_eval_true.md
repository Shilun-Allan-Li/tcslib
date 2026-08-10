<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: Literal.fixedBy_eval_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A fixed literal evaluates to true under the restriction

**Claim.** Let `l : Literal n` and `ρ : Restriction n` with
`Literal.fixedBy l ρ`, i.e. `ρ l.var = some (!l.neg)`. Then for every
`x : Fin n → Bool`, `l.eval (ρ.extend x) = true`.

**Proof.**

1. `unfold Literal.fixedBy at h` exposes `h : ρ l.var = some (!l.neg)`.
2. `simp [Literal.eval, Restriction.extend, h]`: `ρ.extend x` at `l.var` is
   `(ρ l.var).getD (x l.var) = !l.neg`, and `Literal.eval` negates that exactly
   when `l.neg` is true, giving `true` in both polarities.

**Remark.** The mirror image of `Literal.killedBy_eval_false`: "fixed" means the
restriction assigns the satisfying polarity, so the literal is already
determined true and `x` is irrelevant.

**Used in.** `fixedTerm_implies_dtDepth_zero` (same file) and
`canonicalDTree_go_correct` in `Switching/CanonicalDTree.lean`.
