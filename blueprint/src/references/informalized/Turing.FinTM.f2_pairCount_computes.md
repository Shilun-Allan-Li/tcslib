<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_pairCount_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Count Computation

**Claim.** If a finite machine computes $g(x)$ on every bit string $x$ within $T(|x|)$ steps, then the constructed machine computes the specified one-bit pair-count predicate within $T(|x|)+2|x|+5$ steps.

**Proof.** Fix an input $x$. The length-start construction supplies a time $t\le T(|x|)+|x|+4$ and a configuration $c$ in which the simulation of the original machine has finished with output $g(x)$, while the constructed machine is positioned to parse the input (`Turing.FinTM.f2_lenStart`). From this configuration, the length-parse run lemma supplies a further time $r\le |x|+1$ at which the machine halts and outputs the required bit: it is $1$ exactly when parsing succeeds and the second component has length at most the stored bound $|g(x)|$ (`Turing.FinTM.f2_lenParse_run`). The run-addition law combines these phases into a run of length $t+r$ (`Turing.MultiTapeTM.runFrom_add`); the computation characterization identifies its halting state and output with the claimed computation (`Turing.FinTM.computesInTime_iff`). Finally, $t+r\le T(|x|)+2|x|+5$, so monotonicity of the time bound gives the stated time (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.f2_lenStart`, `Turing.FinTM.f2_lenParse_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
