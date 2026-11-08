<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace.lean :: Complexity.LogProg.narm_mem_RL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Programs in Randomized Logarithmic Space

**Claim.** If the register program has polynomially bounded registers, halts on all choice strings of a common input-dependent length, and has the stated one-sided probability gap, then its language belongs to $\text{RL}$.

**Proof.** Use the logarithmic-space simulation theorem (`narm_logspace_ptm`) with the given halting and register-bound hypotheses. It supplies a finite-state nondeterministic machine using logarithmic space which, for each qualifying input and choice length, halts at a common time and has exactly the same output probabilities as the register program. The positive answer probability is therefore at least $\delta$ on inputs in $L$. On inputs outside $L$, the register program answers no with probability one, so the simulated machine outputs the one-bit string $[\mathrm{false}]$ on every choice string of the corresponding length. The positive-error randomized-space theorem (`mem_RSPACE_of_pos`) now applies: the space bound is logarithmic, the acceptance probability on members is at least the positive rational $\delta$, and nonmembers are rejected on every run. Hence $L\in\mathrm{RL}$.

**Key facts.** `Complexity.LogProg.narm_logspace_ptm`, `Randomized.mem_RSPACE_of_pos`.
