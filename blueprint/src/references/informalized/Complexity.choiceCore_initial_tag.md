<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choiceCore_initial_tag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Boundary Tag

**Claim.** The initial configuration, with input-head position $1$, satisfies the virtual boundary-tag condition with tag true.

**Proof.** The initial input-head position has value $1$. It is therefore neither the left boundary value $0$ nor the right boundary value $|x|+1$; in particular, both implications in the virtual boundary-tag condition hold, the second because its premise is false. Hence the tag true is valid initially.
