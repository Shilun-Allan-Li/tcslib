<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Actions Commute with Unary Reinterpretation

**Claim.** Reinterpreting the result of applying an action to a configuration on $x$ as a configuration on the all-ones word of length $|x|$ agrees with applying the same action after unary reinterpretation.

**Proof.** The action updates the state, work tapes, work-tape heads, and output in the same way on either input word, since those components are unaffected by unary reinterpretation. For the input head, both sides apply the same movement to the same head position. The two input words have equal length, so the bounds used to represent the moved position coincide; consequently the resulting input-head positions agree as well. All configuration components are therefore equal.
