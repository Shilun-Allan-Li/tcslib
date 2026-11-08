<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.guideFill_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Filling zero cells changes nothing

**Claim.** For either direction and any guide tape, filling zero cells leaves the tape unchanged.

**Proof.** At every coordinate, the condition for being among the filled cells requires a nonnegative directional coordinate strictly less than $0$, which is impossible. Thus the filled-tape definition always selects the original guide tape value.
