<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepRevCfg_stay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary Backward Sweep State Change

**Claim.** A stationary action that emits no output, makes no work-tape change, and sets the successor state to $q'$ changes the state of the backward-sweep configuration to $q'$ while preserving its input-head position, frontier, stacks, tape contents, and output.

**Proof.** The action's state field is $q'$. Its zero input movement preserves the input-head position, and its zero work-head movement leaves the head at the same frontier. Because it makes no write, the tape function is unchanged; because it emits no symbol, appending its output leaves the output word unchanged. Thus every configuration field agrees with that of the backward-sweep configuration having state $q'$.
