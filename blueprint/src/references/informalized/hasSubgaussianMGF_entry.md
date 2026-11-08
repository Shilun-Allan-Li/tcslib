<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: hasSubgaussianMGF_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sub-Gaussian Rademacher Entries

**Claim.** Each coordinate $\omega\mapsto\omega_{ij}$ under the joint Rademacher product measure has a sub-Gaussian moment-generating function with variance proxy $1$.

**Proof.** The coordinate projection $\omega\mapsto\omega_{ij}$ is measurable. Its distribution under the joint product measure is the Rademacher measure: the entry marginal identity gives this directly. A random variable with this distribution therefore has the same sub-Gaussian bound as the identity function under the Rademacher measure, which is sub-Gaussian with variance proxy $1$. Transporting that bound across the coordinate projection proves the claim.

**Key facts.** `radJointMeasure_entry_marginal`, `hasSubgaussianMGF_id_rademacherReal`.
