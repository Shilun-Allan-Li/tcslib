<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.queryTM_no -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition in the Negative-Answer State

**Claim.** In the negative-answer state, the constructed machine's transition is the answer action emitting false, with no tape movements or writes, and with no successor state.

**Proof.** The negative-answer state is the right-hand sum state indexed by $2$. In that branch of the constructed transition, the test for index $1$ fails and the test for index $2$ succeeds, selecting the answer action for false. By definition, this action leaves the input and work tapes unmoved and unwritten, emits false, and has no successor state.
