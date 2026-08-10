<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dtDepth_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pointwise-equal functions have equal decision-tree depth

**Claim.** For `f g : (Fin n → Bool) → Bool` with `f x = g x` for every `x`,
`dtDepth f = dtDepth g`.

**Proof.** Immediate from `funext h` followed by `rw [h_eq]`: pointwise equality
gives `f = g`, and `dtDepth` is a function of that argument.

**Remark.** A pure plumbing helper. It exists because `dtDepth` is defined by
`Nat.find` over decision trees computing `f` (see `dtDepth`), so the statement is
not a `simp`-visible congruence and callers that produce a function only up to
pointwise equality — typically after `restrictFn` or `CNF.eval` rewriting — need
this explicit step.

**Used in.** `switching_bernoulli_dtDepth_function` and
`depth3_second_stage_bound` (both in `Depth3Switching.lean`), where the CNF
representing a function agrees with it only pointwise.
