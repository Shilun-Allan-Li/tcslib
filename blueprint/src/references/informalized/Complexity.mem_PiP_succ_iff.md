<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.mem_PiP_succ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Characterization of $\Pi^P$

**Claim.** A language belongs to $\Pi_{i+1}^P$ exactly when membership has the stated universal polynomial-witness characterization over a language in $\Sigma_i^P$.

**Proof.** Use complement duality to express membership in $\Pi_{i+1}^P$ as membership of the complement in $\Sigma_{i+1}^P$ (`Complexity.compl_mem_SigmaP_iff`). The successor characterization of the existential class supplies a language in $\Pi_i^P$ and an existential witness condition for that complement (`Complexity.mem_SigmaP_succ_iff`). Complement the auxiliary language, which is then in $\Sigma_i^P$ by complement duality (`Complexity.compl_mem_PiP_iff`). Negating the existential condition changes it into a universal condition over all witnesses of the prescribed length; the double negation on membership in $L$ cancels. These steps give the stated equivalence.

**Key facts.** `Complexity.compl_mem_SigmaP_iff`, `Complexity.mem_SigmaP_succ_iff`, `Complexity.compl_mem_PiP_iff`.
