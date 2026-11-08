<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.incrementTM_run_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running Time for Successful Increment

**Claim.** If incrementing the selected tape's word yields $v$, the machine reaches the done phase with true verdict within $2|w_i|+2$ steps, with no earlier done phase, and stores the updated word family at that time.

**Proof.** Apply the arbitrary-configuration successful-increment result (`incrementTM_run_succ_ofCfg`) to the configuration storing the word family. Its tape-agreement and run-phase hypotheses hold by the definition of that configuration. The result gives completion at time $2m+2$, where $m$ is the length of the initial run of true bits, and rules out an earlier done phase. To compare this time with the required bound, decompose $w_i$ as a run of $p$ true bits followed by either nothing or a false bit and a tail (`catalog_increment_split`). The increment-value formula (`catalog_increment_value`) and the hypothesis that the result is defined rule out the empty-tail case; hence $m=p\leq |w_i|$. Therefore $2m+2\leq 2|w_i|+2$. The same formula identifies $v$ as the incremented word on this decomposition, so the terminal tape contents are exactly those of the family with $w_i$ replaced by $v$.

**Key facts.** `Turing.catalog_increment_split`, `Turing.catalog_increment_value`, `Turing.incrementTM_run_succ_ofCfg`.
