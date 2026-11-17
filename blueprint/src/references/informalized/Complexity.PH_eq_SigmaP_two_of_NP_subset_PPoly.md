<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collapse to the Second Level

**Claim.** If every NP language has polynomial-size Boolean circuit families with fan-in at most two, then $\mathsf{PH}=\Sigma_2^P$.

**Proof.** The circuit hypothesis yields the inclusion $\Pi_2^P\subseteq\Sigma_2^P$ (`Complexity.PiP_two_subset_SigmaP_two_of_NP_subset_PPoly`). The hierarchy-collapse theorem turns such an inclusion at any positive level $i$ into $\mathsf{PH}=\Sigma_i^P$ (`Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`). Apply it with $i=2$ to obtain the stated equality.

**Key facts.** `Complexity.PiP_two_subset_SigmaP_two_of_NP_subset_PPoly`, `Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`.
