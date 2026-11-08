<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterWord_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Counter Iterations

**Claim.** For every Boolean word $w$, applying the counter-word operation zero times returns $w$.

**Proof.** The counter-word operation is defined by iterating a function exactly the specified number of times. Iteration zero is the identity function, so the result is $w$.
