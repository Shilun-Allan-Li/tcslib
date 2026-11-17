<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: memLp_scaled_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square integrability of a scaled entry

**Claim.** For each pair of indices, the function $\omega\mapsto (x_j/\sqrt{k})\omega_{ij}$ belongs to $L^2$ under the joint Rademacher product measure.

**Proof.** Write $c=x_j/\sqrt{k}$. The entry map $\omega\mapsto\omega_{ij}$ is measurable, and its distribution under the joint measure is the one-coordinate Rademacher measure, by the entry marginal identity (radJointMeasure_entry_marginal). Since a Rademacher variable lies in $[-1,1]$ almost surely (rademacherReal_mem_Icc), we have $|c\omega_{ij}|\le |c|$ almost surely. The scaled entry is therefore almost surely bounded and measurable, which implies it belongs to $L^2$ on this probability space.

**Key facts.** `radJointMeasure_entry_marginal`, `rademacherReal_mem_Icc`.
