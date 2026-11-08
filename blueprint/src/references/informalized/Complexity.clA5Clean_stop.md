<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Clean_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Release Wrapper for Clean Computations

**Claim.** If a machine with a positive number of work tapes reaches its designated exit state at a positive time $t\le B(|arg|)$, has not reached that state at any earlier positive time, and there has the specified tape contents and output, then its release wrapper satisfies the clean contract within the bound $B(|arg|)+1$.

**Proof.** Fix an input and argument, and choose the time $t$ and exit computation given by the hypothesis. The wrapper begins in a marked entry state and simulates the original machine. The wrapper simulation lemma (`Complexity.clA5Stop_clean`) shows that after $t+1$ steps its configuration has the marked exit state, the required tape words, and the same output. Since the original run did not visit the exit state at any earlier positive time, this is the wrapper's first halt; formally, the first-halt principle (`Complexity.clA5_call_first_halt`) selects a positive first halting time no later than $t+1$ and identifies its configuration with the one at that time. Therefore this first halt is within $B(|arg|)+1$ and has the prescribed clean configuration.

**Key facts.** `Complexity.clA5Stop_clean`, `Complexity.clA5_call_first_halt`.
