<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.mem_PiP_two_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Characterization of $\Pi_2^P$

**Claim.** A language is in $\Pi_2^P$ exactly when it has a universal polynomial-witness characterization whose paired instances belong to an $\mathsf{NP}$ language.

**Proof.** Rewrite $2$ as $1+1$ and apply the successor characterization of $\Pi^P$ (`Complexity.mem_PiP_succ_iff`). This gives an auxiliary language in $\Sigma_1^P$ together with the stated universal condition. The identity $\Sigma_1^P=\mathsf{NP}$ (`Complexity.SigmaP_one`) replaces that auxiliary class by $\mathsf{NP}$, yielding the result.

**Key facts.** `Complexity.mem_PiP_succ_iff`, `Complexity.SigmaP_one`.
