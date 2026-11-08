<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.P_subset_SigmaP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time in Every Existential Level

**Claim.** For every natural number $i$, every language decidable in polynomial time belongs to the $i$th existential class $\Sigma_i^{\mathsf{P}}$.

**Proof.** At level zero, the existential class is exactly polynomial time (\(\texttt{Complexity.SigmaP\_zero}\)). The existential levels are monotone: if $i \le j$, then $\Sigma_i^{\mathsf{P}} \subseteq \Sigma_j^{\mathsf{P}}$ (\(\texttt{Complexity.SigmaP\_mono}\)). As $0 \le i$, monotonicity from level zero gives the desired inclusion.

**Key facts.** `Complexity.SigmaP_zero`, `Complexity.SigmaP_mono`.
