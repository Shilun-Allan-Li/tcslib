<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_complement_twice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutive Work-Tape Complementation

**Claim.** Complementing every work-tape symbol of a Boolean configuration twice returns exactly the original configuration.

**Proof.** Configurations are equal once their fields agree. The state, input-head position, work-head positions, and output are unchanged by work-symbol complementation. For each tape and cell, the stored optional Boolean is mapped by negation twice; Boolean negation is an involution, and mapping it over an optional symbol leaves a blank blank. Thus the work-tape contents also agree, proving equality of configurations.
