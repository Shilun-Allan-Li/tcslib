<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.queryTM_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition on an Embedded Original State

**Claim.** At an embedded original state, the constructed oracle machine's transition equals the capture transform of the original machine's transition, with the oracle query state as return state.

**Proof.** Unfold the constructed oracle machine's transition at an embedded state. Its state case selects the original-machine branch, whose definition is precisely the capture transform using the inclusion into the enlarged state space and the designated query state as return state. Thus the two actions are definitionally equal for every input symbol and work-tape assignment.
