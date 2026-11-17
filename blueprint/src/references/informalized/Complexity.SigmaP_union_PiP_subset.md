<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.SigmaP_union_PiP_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacent Levels Contain Both Quantifier Classes

**Claim.** For every natural number $i$, the union $\Sigma_i^P\cup\Pi_i^P$ is contained in $\Sigma_{i+1}^P\cap\Pi_{i+1}^P$.

**Proof.** Take a language in the union and split into its two possibilities. If it is in $\Sigma_i^P$, the successive existential-level inclusion places it in $\Sigma_{i+1}^P$ (`SigmaP_subset_SigmaP_succ`), while the existential-to-next-universal inclusion places it in $\Pi_{i+1}^P$ (`SigmaP_subset_PiP_succ`). If instead it is in $\Pi_i^P$, the universal-to-next-existential inclusion gives membership in $\Sigma_{i+1}^P$ (`PiP_subset_SigmaP_succ`), and nesting of the universal levels gives membership in $\Pi_{i+1}^P$ (`PiP_subset_PiP_succ`). In either case it lies in the intersection.

**Key facts.** `Complexity.SigmaP_subset_SigmaP_succ`, `Complexity.SigmaP_subset_PiP_succ`, `Complexity.PiP_subset_SigmaP_succ`, `Complexity.PiP_subset_PiP_succ`.
