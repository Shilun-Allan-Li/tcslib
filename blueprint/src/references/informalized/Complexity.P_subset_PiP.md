<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.P_subset_PiP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time in Every Universal Level

**Claim.** For every natural number $i$, every language decidable in polynomial time belongs to the $i$th universal class $\Pi_i^{\mathsf{P}}$.

**Proof.** At level zero, the universal class is exactly polynomial time (\(\texttt{Complexity.PiP\_zero}\)). The universal levels are monotone: if $i \le j$, then $\Pi_i^{\mathsf{P}} \subseteq \Pi_j^{\mathsf{P}}$ (\(\texttt{Complexity.PiP\_mono}\)). Since $0 \le i$, applying monotonicity to the level-zero equality proves the result.

**Key facts.** `Complexity.PiP_zero`, `Complexity.PiP_mono`.
