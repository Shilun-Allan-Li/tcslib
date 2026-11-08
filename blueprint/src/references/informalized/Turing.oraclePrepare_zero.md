<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oraclePrepare_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Oracle Preparation

**Claim.** For every Boolean input word, tape content, side bit, valid input-head position, and output word, two steps from the bookmark configuration at position zero produce the ready configuration at position zero, with empty argument word and copy state, preserving the input-head position and output.

**Proof.** Expand the two-step run as two successive transitions. In the bookmark state at position zero, the dispatch machine's transition rules place the machine in the required intermediate state and update the work tapes; the next transition produces the ready tape layout and copy state. The input head does not move in either transition, and neither transition emits output. Comparing the resulting state, head position, tape contents, head positions, and output with the stated ready configuration proves equality.
