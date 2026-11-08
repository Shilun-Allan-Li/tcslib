<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: integral_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Rademacher entry

**Claim.** Each entry of the random array has mean zero under the joint Rademacher measure.

**Proof.** Consider the coordinate map that sends an array to its $(i,j)$ entry. The joint measure pushed forward by this map is the one-dimensional Rademacher measure (radJointMeasure_entry_marginal). The integral of the coordinate over the joint measure therefore equals the integral of the identity function over that marginal. The latter integral is zero because the Rademacher distribution assigns equal mass to $-1$ and $1$ (integral_id_rademacherReal).

**Key facts.** `radJointMeasure_entry_marginal`, `integral_id_rademacherReal`.
