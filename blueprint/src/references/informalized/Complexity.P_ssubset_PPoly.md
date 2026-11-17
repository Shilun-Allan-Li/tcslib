<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPoly.lean :: Complexity.P_ssubset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict polynomial–circuit containment

**Claim.** The class $\mathsf{P}$ is a proper subset of the class of languages decided by polynomial-size Boolean circuit families with fan-in at most two.

**Proof.** The inclusion of $\mathsf{P}$ in the stated circuit class is given by $\texttt{Complexity.P\_subset\_PPoly}$. The general strictness result says that whenever this inclusion holds, it is proper (\texttt{Complexity.P\_ssubset\_PPoly\_of\_subset}); applying it gives the claim.

**Key facts.** `Complexity.P_ssubset_PPoly_of_subset`, `Complexity.P_subset_PPoly`.
