<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepCfg_stay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary Sweep Update

**Claim.** The stationary action changes the state to $q'$ and leaves the input position, tape contents, work-head position, and output unchanged.

**Proof.** The action writes nothing, moves neither head, and emits no symbol. Hence the input position and work-head position remain fixed, and the tape function is unchanged. Its successor state is $q'$, while appending the empty output word leaves $out$ unchanged. These fieldwise equalities give the asserted configuration equality.
