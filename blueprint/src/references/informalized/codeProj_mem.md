<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: codeProj_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The code projector lands in the code

**Claim.** For `C : Submodule ℂ (Hn n)` and any `x : Hn n`, the projected vector
lies in the code: `codeProj C x ∈ C`. No hypothesis on `x`.

**Proof.** Two steps.

1. `simp only [codeProj_apply]` rewrites the goal to
   `↑(Submodule.orthogonalProjection C x) ∈ C`.
2. `Submodule.coe_mem` closes it: the projection already has type `↥C`, so its
   coercion is a member by construction.

**Remark.** The content is entirely in the retyping — once `codeProj` is
recognised as the coercion of a `↥C`-valued map, membership is definitional. A
deliberately granular helper.

**Used in.** `codeProj_idempotent`, where it supplies the hypothesis for
`codeProj_eq_self_of_mem`.
