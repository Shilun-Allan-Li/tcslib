<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.inBPP_polyTimeModel_iff_mem_P_of_P_eq_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP and P under P equals NP

**Claim.** If $\mathrm{P}=\mathrm{NP}$, then a language belongs to BPP in the polynomial-time verifier model if and only if it belongs to $\mathrm{P}$.

**Proof.** For the forward implication, the Sipser–Gács theorem places every such language in $\Sigma_2^P$. The polynomial hierarchy collapses to $\mathrm{P}$ when $\mathrm{P}=\mathrm{NP}$, so $\mathrm{PH}=\mathrm{P}$; since $\Sigma_2^P\subseteq\mathrm{PH}$, the language is in $\mathrm{P}$. Conversely, every language in $\mathrm{P}$ belongs to BPP in this verifier model.

**Key facts.** `Randomized.sipser_gacs_polyTime`, `Complexity.PH_eq_P_of_P_eq_NP`, `Complexity.SigmaP_subset_PH`, `Randomized.inBPP_polyTimeModel_of_mem_P`.
