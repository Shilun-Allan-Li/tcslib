<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: totalInfluence_eq_sum_influences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Total influence is the sum of the individual influences

**Claim.** For `f : BooleanFunc n`, `totalInfluence f = ∑ i, influence i f`.

**Proof.** `rfl`. In `BooleanAnalysis.Basic` the definition of `totalInfluence` is
literally `∑ i : Fin n, influence i f`, so the two sides are the same term and no
rewriting happens.

**Remark.** A restatement kept for readability — it lets a proof cite `I[f] = ∑_i Inf_i[f]`
by name instead of unfolding a definition. It is currently **unused**: nothing in
the repository references it, and the places in `KKL.lean` that need the identity
(e.g. `cauchy_schwarz_influences`, `max_influence_from_sum_sq`) reach for
`simp only [totalInfluence]` or a bare `rfl` instead.
