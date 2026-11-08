<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.BPP_PTM_eq_P_of_P_eq_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Equals P Under P Equals NP

**Claim.** If $\mathrm{P}=\mathrm{NP}$, then $\mathrm{BPP}=\mathrm{P}$.

**Proof.** Assume $\mathrm{P}=\mathrm{NP}$. Extensionality reduces the class equality to a statement about each language. For any language, membership in BPP is equivalent to the verifier-based BPP condition (`mem_BPP_PTM_iff`). Under the assumed equality of deterministic polynomial time and nondeterministic polynomial time, that verifier-based condition is equivalent to membership in $\mathrm{P}$ (`inBPP_polyTimeModel_iff_mem_P_of_P_eq_NP`). Composing the equivalences proves the result.

**Key facts.** `Randomized.mem_BPP_PTM_iff`, `Randomized.inBPP_polyTimeModel_iff_mem_P_of_P_eq_NP`.
