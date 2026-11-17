<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPoly.lean :: Complexity.P_ne_NP_of_not_NP_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit lower bounds separate classes

**Claim.** If some language in $\mathsf{NP}$ is not decidable by any polynomial-size Boolean circuit family of fan-in at most two, then $\mathsf{P}\ne\mathsf{NP}$.

**Proof.** Suppose instead that $\mathsf{P}=\mathsf{NP}$. Every language in $\mathsf{P}$ has polynomial-size circuits of fan-in at most two (\texttt{Complexity.P\_subset\_PPoly}); the assumed equality therefore makes every language in $\mathsf{NP}$ belong to that circuit class. This contradicts the hypothesis that $\mathsf{NP}$ is not contained in the circuit class.

**Key facts.** `Complexity.P_subset_PPoly`.
