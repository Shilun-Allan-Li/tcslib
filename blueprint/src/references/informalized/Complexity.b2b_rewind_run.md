<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_rewind_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind Run to the Left Boundary

**Claim.** Starting in the rewind machine’s start state, there is a time no greater than the current input-head position plus two when the machine halts at input-head position $1$. Throughout the run, every work-tape head position stays unchanged.

**Proof.** The rewind machine first moves its input head left and enters its scanning state. In that state it continues moving left while it reads an input symbol; at the left boundary it moves right once and halts. The rewind-head theorem (`Turing.FinTM.rewind_heads`), applied with these transition rules, gives a time at most the initial input-head position plus two, the halted configuration at position $1$ with all other fields unchanged, and preservation of every work-head position throughout.

**Key facts.** `Turing.FinTM.rewind_heads`.
