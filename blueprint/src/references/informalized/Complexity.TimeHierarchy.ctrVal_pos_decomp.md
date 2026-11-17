<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrVal_pos_decomp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First True Digit in a Positive-Value List

**Claim.** If a Boolean list has nonzero binary value, it consists of some number of false digits followed by a true digit and a remaining list.

**Proof.** Induct on the list. The empty list cannot have nonzero value. For a nonempty list, if its first digit is true, it already has the required form with zero initial false digits. If its first digit is false, the remaining list must have nonzero value: otherwise the defining recurrence for the value would make the whole list's value zero. Apply the induction hypothesis to the tail, then include the initial false digit, increasing the number of initial false digits by one.
