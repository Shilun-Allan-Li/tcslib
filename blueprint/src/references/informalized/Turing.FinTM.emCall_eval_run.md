<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_eval_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation by the Capture-Wrapped Evaluator

**Claim.** If $b$ correctly marks the input-head boundary of a configuration $c$ of $M$, and the run from $c$ remains live before time $t$, then for some valid tag $b'$ the capture-wrapped evaluator run for $t$ steps matches the evaluator configuration associated with $M$'s time-$t$ configuration, with the same physical input-head position.

**Proof.** First, the buffered-composition simulation theorem (\texttt{bufferedSecondCfg\_run}) tracks the run of $M$ for $t$ steps. It supplies a tag at each time that correctly marks the simulated input-head boundary and identifies the composed machine's configuration with the corresponding buffered configuration. In particular, at every $j<t$ this composed configuration is not halted, because the original run is live there. The capture simulation theorem (\texttt{capture\_run}) now applies: while the composed machine remains live before time $t$, the capture-wrapped host follows it for those $t$ steps. At time $t$, use the tag and configuration identification from the buffered simulation to rewrite the host's result as the evaluator configuration associated with the time-$t$ configuration of $M$. The physical input-head position is preserved throughout these simulations.

**Key facts.** `Turing.FinTM.bufferedSecondCfg_run`, `Turing.capture_run`.
