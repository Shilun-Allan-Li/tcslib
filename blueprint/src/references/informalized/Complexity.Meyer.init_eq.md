<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.init_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial configuration of the tabulating machine

**Claim.** The initial configuration of the tabulating machine has its simulated state and output register initialized, its input head at the clamped position $1$, blank work tapes, work-tape heads at the origin, and empty output.

**Proof.** Expand the initial configuration and the explicit configuration description. Both have the same initial state, and both have empty output. The input-head positions agree because clamping $1$ to the range from $0$ through $|y|+1$ leaves it at $1$; the index used for the initial selector is valid since the selector count is positive (`nbitsOf_pos`). The work-tape functions agree pointwise: the simulated tapes are blank and their heads are at zero, while each of the three auxiliary tapes is also blank with its head at zero. These componentwise equalities give equality of the configurations.

**Key facts.** `Complexity.Meyer.nbitsOf_pos`.
