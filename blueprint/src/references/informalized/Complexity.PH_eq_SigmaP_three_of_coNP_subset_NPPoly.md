<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.PH_eq_SigmaP_three_of_coNP_subset_NPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collapse to the Third Level

**Claim.** If every coNP language has polynomial-size fan-in-two circuits with existentially quantified auxiliary input bits, then $\mathsf{PH}=\Sigma_3^P$.

**Proof.** The assumed circuit representation implies the level-three inclusion $\Pi_3^P\subseteq\Sigma_3^P$ (`Complexity.PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly`). Apply the hierarchy-collapse result at level three: for any $i\ge1$, this inclusion forces $\mathsf{PH}=\Sigma_i^P$ (`Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`). Since $3\ge1$, the conclusion is $\mathsf{PH}=\Sigma_3^P$.

**Key facts.** `Complexity.PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly`, `Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`.
