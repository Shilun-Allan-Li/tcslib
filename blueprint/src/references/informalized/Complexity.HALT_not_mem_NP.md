<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.HALT_not_mem_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Halting Language Is Not in NP

**Claim.** For every effective machine representation scheme $c$, the language of inputs on which $\mathrm{HALT}_c$ returns true is not in NP.

**Proof.** Assume the halting language belongs to NP. Since NP is contained in EXP (Complexity.NP_subset_EXP), it has an exponential-time decider $M$, with time bound of the form $a\,2^{n^d}$. The indicator of the halting language is exactly the Boolean function $s\mapsto\mathrm{HALT}_c(s)$: membership gives true, and nonmembership gives false. Therefore $M$ computes the one-bit output $[\mathrm{HALT}_c(s)]$ within its time bound; forgetting the bound still shows that this function is computable (Turing.FinTM.ComputesFunInTime.computes). This contradicts the uncomputability of the halting function (Complexity.HALT_not_computable). Thus the halting language is not in NP.

**Key facts.** `Complexity.NP_subset_EXP`, `Complexity.HALT_not_computable`, `Turing.FinTM.ComputesFunInTime.computes`.
