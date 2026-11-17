<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Initial Configuration

**Claim.** Reinterpreting the normalized machine's initial configuration on $x$ as a configuration on the all-ones word of length $|x|$ gives $M$'s initial configuration on that word.

**Proof.** Both initial configurations have the initial state, blank work tapes, work-head positions at zero, and empty output. Their input-head positions are also equal: each is the first input cell, represented by position $1$. The reinterpretation retains that position, so all components agree.
