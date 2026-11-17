<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_lengthBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computing Input Length in Binary

**Claim.** A finite Turing machine computes the little-endian binary representation of the length of every Boolean input word in time bounded by a constant multiple of its length plus one.

**Proof.** The identity function on natural numbers is time-constructible (`Complexity.timeConstructible_id`). Unpacking this fact supplies a finite machine and a constant that compute the binary representation of the input natural number within the corresponding linear time bound. Apply that machine to the input length: the resulting output is $\mathrm{Nat.bits}(|x|)$, as required.

**Key facts.** `Complexity.timeConstructible_id`.
