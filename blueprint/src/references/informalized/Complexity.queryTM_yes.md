<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.queryTM_yes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition in the Positive-Answer State

**Claim.** In the positive-answer state, the constructed machine's transition is the answer action emitting true, with no tape movements or writes, and with no successor state.

**Proof.** The positive-answer state is the right-hand sum state indexed by $1$. In that branch of the constructed transition, the first index test succeeds, selecting the answer action for true. By definition, this action leaves the input and work tapes unmoved and unwritten, emits true, and has no successor state.
