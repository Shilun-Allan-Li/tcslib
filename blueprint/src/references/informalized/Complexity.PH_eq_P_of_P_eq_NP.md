<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.PH_eq_P_of_P_eq_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Hierarchy Collapse

**Claim.** If $\mathsf{P}=\mathsf{NP}$, then $\mathsf{PH}=\mathsf{P}$.

**Proof.** First identify the first existential and universal levels. The level-one characterizations give $\Sigma_1^P=\mathsf{NP}$ and $\Pi_1^P=\mathrm{coNP}$ (`Complexity.SigmaP_one`, `Complexity.PiP_one`). Under the hypothesis $\mathsf{P}=\mathsf{NP}$, the complement classes therefore agree, by the fact that this equality implies $\mathsf{NP}=\mathrm{coNP}$ (`Complexity.NP_eq_coNP_of_P_eq_NP`). Hence $\Sigma_1^P=\Pi_1^P$. The hierarchy collapse theorem says that equality of these two classes at any level $i\ge1$ implies $\mathsf{PH}=\Sigma_i^P$ (`Complexity.PH_eq_SigmaP_of_SigmaP_eq_PiP`). Apply it at level one, then use $\Sigma_1^P=\mathsf{NP}=\mathsf{P}$ to conclude $\mathsf{PH}=\mathsf{P}$.

**Key facts.** `Complexity.SigmaP_one`, `Complexity.PiP_one`, `Complexity.NP_eq_coNP_of_P_eq_NP`, `Complexity.PH_eq_SigmaP_of_SigmaP_eq_PiP`.
