<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPayload_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computing on the Extracted Payload

**Claim.** If a finite machine computes a total function $g$ within a monotone time bound $T_g$, then buffered composition of the pair-component extractor with that machine computes $g$ applied to the parser's second component, using the empty word when parsing is undefined, within $6(n+1)+T_g(n)+1$ steps on inputs of length $n$.

**Proof.** Fix an input $x$, and let $y$ be the second component returned by the aligned pair parser, or the empty word if parsing is undefined. The pair-extraction machine, with its second-component output enabled, computes $y$ in $5(|x|+1)$ steps. The extracted payload has length at most $|x|$. The buffered-start result therefore gives a time $a\le 5(|x|+1)+|y|+2$ at which the composed machine has finished extraction and is in a configuration representing the initial configuration of the machine for $g$ on input $y$. The buffered-run result says that the next $T_g(|y|)$ steps simulate that machine's run, while retaining the simulated state and output in the buffered configuration. Since that machine computes $g(y)$ by its time bound, the composed machine has halted with output $g(y)$ after a total of $a+T_g(|y|)$ steps. The payload length bound and monotonicity give $T_g(|y|)\le T_g(|x|)$. Finally, $a\le 6(|x|+1)+1$ because $|y|\le |x|$, so the total is at most $6(|x|+1)+T_g(|x|)+1$.

**Key facts.** `Turing.FinTM.pairExtractTM_computes`, `Turing.FinTM.catalogPayload_length`, `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
