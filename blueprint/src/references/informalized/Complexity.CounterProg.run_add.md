<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.run_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Counter-Program Runs

**Claim.** Running the counter program for $a+b$ steps from any abstract state gives the same state as running it for $a$ steps and then for $b$ further steps.

**Proof.** The run is the $(a+b)$-fold iterate of the one-step transition. Iteration by a sum composes the corresponding iterates; the proof writes the sum in the reversed order, $b+a$, which is equal to $a+b$ by commutativity of addition. The iterate-composition identity therefore gives the run for $b$ steps applied to the state reached after $a$ steps, as claimed.
