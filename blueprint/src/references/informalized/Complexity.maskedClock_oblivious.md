<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.maskedClock_oblivious -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Obliviousness of the Masked Clock

**Claim.** For any two inputs of equal length, the masked machine has the same input-head position and work-tape head positions at every time.

**Proof.** Fix inputs $x,y$ of equal length and a time $t$. The lockstep identity (`Complexity.maskedClock_lockstep`) identifies the masked machine's configuration after $t$ steps on either input with the original machine's configuration after $t$ steps on the constant word of the corresponding input length, filled with the masking symbol. Since $x$ and $y$ have the same length, these constant words are identical. Their original-machine configurations therefore agree, so their input-head positions and work-tape head positions agree as well. This argument applies at every time, including after halting.

**Key facts.** `Complexity.maskedClock_lockstep`.
