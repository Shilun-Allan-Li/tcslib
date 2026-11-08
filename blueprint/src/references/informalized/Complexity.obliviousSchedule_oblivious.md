<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.obliviousSchedule_oblivious -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Obliviousness of the schedule

**Claim.** For any two inputs of equal length and any time, the schedule machine has the same input-head position and work-tape head positions on both inputs.

**Proof.** The schedule’s transition depends on the scanned input symbol only through the constant map that replaces every symbol by `false`. Thus, for fixed state and work-tape contents, its transition is unchanged when the scanned input symbol changes. The input-insensitivity criterion (`inputInsensitive_oblivious`) says that a machine with this property has head positions determined solely by input length and time. Applying it gives the required agreement of both the input head and all work-tape heads.

**Key facts.** `Complexity.inputInsensitive_oblivious`.
