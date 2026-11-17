<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_dec_underflow_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of decrement underflow

**Claim.** If fixed-width decrement of $w$ is undefined, every entry of $w$ is false, so the initial segment of false entries has length $|w|$.

**Proof.** The underflow clause of the decrement specification (`counter_dec_spec`) identifies $w$ with the list of $|w|$ false entries. The initial segment of false entries in that replicated list has length $|w|$ (`sc_takeWhile_replicate`), giving the claimed equality.

**Key facts.** `Turing.counter_dec_spec`, `Turing.sc_takeWhile_replicate`.
