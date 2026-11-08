<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.SigmaP_subset_SigmaP_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Existential Levels Are Nested

**Claim.** For every natural number $i$, every language in $\Sigma_i^P$ belongs to $\Sigma_{i+1}^P$.

**Proof.** The proof separates the base level from the positive levels. At level zero, $\Sigma_0^P=\mathsf P$ and $\Pi_0^P=\mathsf P$ (`SigmaP_zero`, `PiP_zero`), so the inclusion follows from the universal-to-next-existential inclusion at level zero (`PiP_subset_SigmaP_succ`). At a successor level, write a member of $\Sigma_{i+1}^P$ in its quantified form: it has a polynomial certificate length and a base language in $\Pi_i^P$ (`mem_SigmaP_succ_iff`). By induction the base language also belongs to $\Sigma_{i+1}^P$. Reusing the same certificate length and the same membership condition therefore gives the required description at the next existential level, again by that characterization.

**Key facts.** `Complexity.SigmaP_zero`, `Complexity.PiP_zero`, `Complexity.PiP_subset_SigmaP_succ`, `Complexity.mem_SigmaP_succ_iff`.
