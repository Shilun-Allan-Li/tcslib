<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Meyer.lean :: Complexity.EXP_eq_SigmaP_two_of_EXP_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Time Equals Two-Level Existential Polynomial Time

**Claim.** If every language in $\mathrm{EXP}$ has polynomial-size Boolean circuits, then $\mathrm{EXP}=\Sigma_2^P$.

**Proof.** The proof takes the two class inclusions in turn. Under the circuit-size hypothesis, `EXP_subset_SigmaP_two_of_EXP_subset_PPoly` gives $\mathrm{EXP}\subseteq\Sigma_2^P$. In the reverse direction, `SigmaP_two_subset_EXP` gives $\Sigma_2^P\subseteq\mathrm{EXP}$ without needing the hypothesis. The two inclusions establish equality.

**Key facts.** `Complexity.EXP_subset_SigmaP_two_of_EXP_subset_PPoly`, `Complexity.SigmaP_two_subset_EXP`.
