<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/CoNP.lean :: Complexity.NP_eq_coNP_of_P_eq_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Equals coNP When P Equals NP

**Claim.** If $\mathrm{P}=\mathrm{NP}$, then $\mathrm{NP}=\mathrm{coNP}$.

**Proof.** Prove both inclusions. For $L\in\mathrm{NP}$, the assumed equality puts $L$ in P; closure of P under complement then gives $L^c\in\mathrm{P}=\mathrm{NP}$, so $L\in\mathrm{coNP}$. Conversely, if $L\in\mathrm{coNP}$, then $L^c\in\mathrm{NP}=\mathrm{P}$. Complement closure gives $L=(L^c)^c\in\mathrm{P}=\mathrm{NP}$ (`compl_mem_P`).

**Key facts.** `Complexity.compl_mem_P`.
