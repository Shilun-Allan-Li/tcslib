<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Meyer.lean :: Complexity.not_EXP_subset_PPoly_of_P_eq_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Time Exceeds Polynomial Circuit Size

**Claim.** If $\mathrm{P}=\mathrm{NP}$, then there is a language in exponential time that cannot be decided by any family of Boolean circuits of polynomial size.

**Proof.** Assume, for contradiction, that every language in exponential time has polynomial-size circuits. The exponential-time-to-second-level inclusion theorem (`EXP_subset_SigmaP_two_of_EXP_subset_PPoly`) then puts all of $\mathrm{EXP}$ in $\Sigma_2^{\mathrm P}$. This class is contained in the polynomial hierarchy (`SigmaP_subset_PH`), and under $\mathrm P=\mathrm{NP}$ the polynomial hierarchy collapses to $\mathrm P$ (`PH_eq_P_of_P_eq_NP`). Consequently $\mathrm{EXP}\subseteq\mathrm P$. Since $\mathrm P\subseteq\mathrm{EXP}$ (`P_subset_EXP`), the two classes would be equal, contradicting their known separation (`P_ne_EXP`). Therefore the assumed circuit inclusion is impossible.

**Key facts.** `Complexity.EXP_subset_SigmaP_two_of_EXP_subset_PPoly`, `Complexity.SigmaP_subset_PH`, `Complexity.PH_eq_P_of_P_eq_NP`, `Complexity.P_subset_EXP`, `Complexity.P_ne_EXP`.
