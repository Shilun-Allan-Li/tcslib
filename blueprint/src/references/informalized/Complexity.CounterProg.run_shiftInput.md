<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgInput.lean :: Complexity.CounterProg.run_shiftInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Prefix Shift Invariance

**Claim.** For any input prefix and suffix, shifting the starting read position by the prefix length while running on their concatenation gives the same state as running on the suffix and then shifting the resulting read position by that length.

**Proof.** Induct on the number of steps, generalizing over the starting state. At zero steps the equality follows directly from the definition of the shift. For the successor case, decompose each run into one step followed by the remaining run (`Complexity.CounterProg.run_succ`). The one-step shift law (`Complexity.CounterProg.step_shiftInput`) identifies the step on the concatenated input from the shifted state with the shifted step on the suffix. The induction hypothesis then identifies the remaining runs, proving the desired equality.

**Key facts.** `Complexity.CounterProg.run_succ`, `Complexity.CounterProg.step_shiftInput`.
