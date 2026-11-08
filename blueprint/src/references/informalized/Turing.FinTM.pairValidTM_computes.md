<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairValidTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-code validity tester time bound

**Claim.** For every finite Boolean word $x$, the pair-code validity tester halts after exactly $|x|+1$ steps, outputs the one-bit word indicating whether the aligned pair parser successfully decodes $x$, and uses some natural number of work-tape cells.

**Proof.** The run lemma `pairValid_run`, applied with the entire input as the unprocessed suffix, gives a halting time $t\le |x|+1$ and output $[(\operatorname{pairDecode}x).\operatorname{isSome}]$ from the initial scan configuration. This scan configuration is the machine's initial configuration: with zero work tapes, it suffices to compare state, input position, and output (`Cfg.ext_zero_tapes`). By the computation characterization (`computesInTime_iff`), the run thus witnesses computation at time $t$, including a space usage value. Monotonicity (`ComputesInTime.mono`) extends the computation to time $|x|+1$.

**Key facts.** `Turing.FinTM.pairValid_run`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
