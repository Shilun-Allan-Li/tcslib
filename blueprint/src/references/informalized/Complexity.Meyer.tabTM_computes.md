<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTab.lean :: Complexity.Meyer.tabTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Tabulation Machine Computes the Function

**Claim.** The tabulation machine computes the function that maps each Boolean word to the one-bit output containing its tabulation-function value, within the stated time bound.

**Proof.** Fix an input word $y$ and split according to whether parsing it as a query succeeds.

1. If parsing fails, the setup result supplies a halting run with output $[\mathrm{false}]$ in at most $|y|+1$ steps (`Complexity.Meyer.tabTM_setup`). By the definition of the tabulation function on a parse failure, this is the required output. The linear bound is at most $10(|y|+1)2^{|y|}$.

2. If parsing succeeds with fields $bits,t,a,x$, setup reaches the decoding configuration within $2|y|+4$ steps. The configuration equality identifying the abstract and concrete setup states lets us apply the machine's simulation phases from that point. The loop-run result simulates the original machine for the time represented by $t$, ending with its resulting configuration and output summary (`Complexity.Meyer.loop_run`). The walk-run result then performs the requested selector lookahead and halts with the corresponding selector answer as its one-bit output (`Complexity.Meyer.walk_run`). Concatenating these phases uses the run-addition law (`Turing.MultiTapeTM.runFrom_add`), and the query evaluation agrees with the tabulation function in the successful parse branch. The standard characterization of computation by a halting run with the required output gives computation at the concatenated time (`Turing.FinTM.computesInTime_iff`); monotonicity extends this to the advertised bound (`Turing.FinTM.ComputesInTime.mono`).

For the estimate, successful parsing bounds both $|t|$ and $|a|$ by $|y|$ (`Complexity.Meyer.parseQ_length`). The binary counter value of a word is less than the corresponding power of two (`Complexity.Meyer.ctrVal_lt`), and these facts bound the loop and walk durations by a constant multiple of $(|y|+1)2^{|y|}$. Adding the setup cost gives at most $10(|y|+1)2^{|y|}$. The initial virtual-tag condition needed to start the simulation is supplied by `Complexity.Meyer.init_tag`.

**Key facts.** `Complexity.Meyer.tabTM_setup`, `Complexity.Meyer.acfg_eq_lcfg`, `Complexity.Meyer.loop_run`, `Complexity.Meyer.walk_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.Meyer.parseQ_length`, `Complexity.Meyer.ctrVal_lt`, `Complexity.Meyer.init_tag`.

**Caveat.** The source's final arithmetic combines detailed phase bounds by nonlinear arithmetic; the supplied statements give the relevant bounds, but not the intermediate numerical inequalities explicitly.
