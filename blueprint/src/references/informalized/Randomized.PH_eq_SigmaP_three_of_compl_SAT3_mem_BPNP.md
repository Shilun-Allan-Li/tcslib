<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Randomized.PH_eq_SigmaP_three_of_compl_SAT3_mem_BPNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Third-Level Collapse of PH

**Claim.** If the complement of $3$-CNF satisfiability belongs to $\mathrm{BPNP}$, then $\mathrm{PH}=\Sigma_3^P$.

**Proof.** The hypothesis that the complement of $3$-CNF satisfiability belongs to $\mathrm{BPNP}$ implies that every language in $\mathrm{coNP}$ has a polynomial-size circuit representation of the stated kind ($\mathrm{coNP\_subset\_NPPoly\_of\_compl\_SAT3\_mem\_BPNP}$). The collapse theorem for this circuit containment then gives $\mathrm{PH}=\Sigma_3^P$ ($\mathrm{PH\_eq\_SigmaP\_three\_of\_coNP\_subset\_NPPoly}$).

**Key facts.** `Randomized.coNP_subset_NPPoly_of_compl_SAT3_mem_BPNP`, `Complexity.PH_eq_SigmaP_three_of_coNP_subset_NPPoly`.
