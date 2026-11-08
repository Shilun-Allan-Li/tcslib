<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.visitedByTapeHead_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Visited Cells

**Claim.** If $t\leq t'$, then every cell visited through time $t$ is also visited through time $t'$.

**Proof.** A cell in the visited set through time $t$ is the tape-head position at some time $j\leq t$. Since $t\leq t'$, the same time satisfies $j\leq t'$. That position therefore appears among the cells visited through time $t'$.
