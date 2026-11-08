<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.callTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded clean call computation

**Claim.** If $M$ halts on argument $a$ with output $c$ after $T$ steps, then the call machine reaches its specified exit configuration in a positive number of steps bounded by $(24+13k)(T+|a|+|c|+1)$, with the requested tape and output contents, and does not reach that exit state earlier.

**Proof.** This is exactly the previously established bounded execution result for the call machine (`emCall_first`). Apply it to the given computation of $M$ on $a$ with output $c$ in time $T$. The lemma supplies a positive time within the stated bound, proves the exit state is absent at every earlier time, and identifies the configuration at that time. The entry state and exit state used by the theorem are the call machine's initial state and the designated state with index $5$, respectively; unfolding those definitions gives the theorem's stated configuration. The supplied run result also gives the requested output and tape contents according to the parameter $e$.

**Key facts.** `Turing.FinTM.emCall_first`.
