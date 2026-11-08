<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.asg_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Empty-Depth Assignment

**Claim.** For every natural number $S$, the assignment function at depth $0$ is constantly false.

**Proof.** At any index $v$, the condition $v<0$ is false. The assignment is defined as the conjunction of this condition with a bit test, so its value is false regardless of $S$ or the bit test. Thus it is the constantly false function.
