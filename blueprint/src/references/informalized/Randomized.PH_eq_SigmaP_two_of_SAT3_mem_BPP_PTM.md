<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.PH_eq_SigmaP_two_of_SAT3_mem_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Second-Level Collapse of PH

**Claim.** If $3$-CNF satisfiability belongs to the polynomial-time bounded-error probabilistic class $\mathrm{BPP}_{\mathrm{PTM}}$, then $\mathrm{PH}=\Sigma_2^P$.

**Proof.** The assumption that $3$-CNF satisfiability lies in $\mathrm{BPP}_{\mathrm{PTM}}$ yields its membership in the polynomial-time verifier formulation of $\mathrm{BPP}$ ($\mathrm{inBPP\_of\_mem\_BPP\_PTM}$). Applying the polynomial-hierarchy collapse theorem under that verifier-model hypothesis gives $\mathrm{PH}=\Sigma_2^P$ ($\mathrm{PH\_eq\_SigmaP\_two\_of\_inBPP\_SAT3}$).

**Key facts.** `Randomized.inBPP_of_mem_BPP_PTM`, `Randomized.PH_eq_SigmaP_two_of_inBPP_SAT3`.
