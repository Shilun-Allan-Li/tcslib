<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.exists_stepClockTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-time clock simulation

**Claim.** A deterministic Boolean machine can be simulated with one additional clock tape so that the simulator detects the first halt or state satisfying the predicate by the encoded time bound, or reports timeout if none occurs, with the stated linear time bounds and without entering either terminal-state family earlier.

**Proof.** Apply the clock-simulation construction for an arbitrary alphabet to the identity embedding of the Boolean alphabet. This supplies the finite simulator, an embedding of the original states, and distinct finish and timeout states, together with both endpoint guarantees. The construction's clock-tape record uses the mapped word; for the identity embedding this is just the original word, so the given tape hypothesis is exactly the one required. Specialize the two guarantees to a first stopping time and to the absence of any stopping time through the deadline, respectively. Their endpoint and no-earlier-terminal-state conclusions give the desired alternatives; the auxiliary tape content at the endpoint is immaterial and can be existentially chosen.

**Key facts.** `Turing.exists_stepClockTMVia`.
