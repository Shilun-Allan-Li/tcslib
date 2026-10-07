<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: pcl_none_implies_rho_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Variables still free after processing a clause were free before

**Claim.** For any literal-with-index list `lits`, path `path` and restrictions
`ρ₀ σ`, if the updated `ρ₀`-component of `processClauseLits lits path ρ₀ σ`
(i.e. `.2.1`) is `none` at `v`, then `ρ₀ v = none`.

**Proof.** Contrapositive, in two tactic lines: `by_contra` + `push_neg` turn
the goal into `ρ₀ v ≠ none`, and `processClauseLits_rho_ne_none` says the
processed `ρ₀` is then also `≠ none` at `v` — contradicting the hypothesis
(`absurd`).

**Used in.** `go_roundtrip_gen`, where every hypothesis about the *pre*-clause
restriction `ρ₀` (freeness of `σ`, the `hA`/`hB` agreements) has to be re-derived
for the *post*-clause restriction `pcl.2.1`; this lemma is the standing bridge.
