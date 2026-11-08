<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.PiP_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Universal Polynomial Hierarchy Level

**Claim.** The first universal polynomial hierarchy level equals coNP: $\Pi_1^P=\mathrm{coNP}$.

**Proof.** For an arbitrary language $L$, membership in $\Pi_1^P$ means that its complement belongs to $\Sigma_1^P$. The first-level characterization identifies $\Sigma_1^P$ with $\mathrm{NP}$, so this is equivalent to the complement of $L$ belonging to $\mathrm{NP}$, which is exactly membership in coNP. Since this equivalence holds for every $L$, the classes are equal.

**Key facts.** `Complexity.SigmaP_one`.
