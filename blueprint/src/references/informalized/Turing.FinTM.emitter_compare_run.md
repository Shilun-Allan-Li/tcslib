<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_compare_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Comparator Run

**Claim.** Starting in the scan phase with register true and both word heads at zero, the comparator reaches the return phase after $2(\max(|u|,|v|)+1)$ steps, with register equal to the truth value of $u=v$ and both heads at zero; the other configuration data are as initially specified.

**Proof.** Put $l=\max(|u|,|v|)$. The forward-scan result says that after $l$ steps the machine remains in the scan phase, its register records whether the length-$l$ prefixes agree, and both heads are at $l$ (`Turing.FinTM.emitter_compare_scan`). Since both words have length at most $l$, these prefixes are the full words, so the register is the truth value of $u=v$. At that position both tapes are blank, as expressed by the list lookup facts and the identification of a natural tape position with the corresponding optional list entry (`Turing.FinTM.bufferTape_nat`). The scan transition therefore enters the rewind phase and moves both heads back to $l-1$, preserving the register. The run decomposition into successive time intervals (`Turing.MultiTapeTM.runFrom_add`) now combines the first $l$ steps, this transition, and the rewind: the rewind result (`Turing.FinTM.emitter_compare_rewind`) takes $l+1$ further steps to reach the return phase with heads zero and register unchanged. The total is $(l+1)+(l+1)=2(l+1)$.

**Key facts.** `Turing.FinTM.emitter_compare_scan`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.emitter_compare_rewind`, `Turing.moveInputPos_zero`.
