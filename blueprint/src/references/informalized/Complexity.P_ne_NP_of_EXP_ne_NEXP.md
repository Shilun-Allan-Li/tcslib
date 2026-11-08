<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.P_ne_NP_of_EXP_ne_NEXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional polynomial-time separation

**Claim.** If $\mathrm{EXP}\ne\mathrm{NEXP}$, then $\mathsf{P}\ne\mathsf{NP}$.

**Proof.** Assume for contradiction that $\mathsf{P}=\mathsf{NP}$. The implication that equality of these classes forces $\mathrm{EXP}=\mathrm{NEXP}$ (\texttt{Complexity.EXP\_eq\_NEXP\_of\_P\_eq\_NP}) then contradicts the hypothesis $\mathrm{EXP}\ne\mathrm{NEXP}$.

**Key facts.** `Complexity.EXP_eq_NEXP_of_P_eq_NP`.
