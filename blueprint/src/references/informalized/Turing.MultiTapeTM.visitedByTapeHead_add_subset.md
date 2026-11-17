<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.MultiTapeTM.visitedByTapeHead_add_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Cells Across Consecutive Blocks

**Claim.** The cells visited through step $T_1+T_2$ are contained in the union of the cells visited through step $T_1$ and those visited for $T_2$ steps from the configuration at time $T_1$.

**Proof.** A cell in the visited set through time $T_1+T_2$ is the tape-head position at some time $u\leq T_1+T_2$. If $u\leq T_1$, it belongs to the first visited set. Otherwise, write $u=T_1+(u-T_1)$, where $u-T_1\leq T_2$. The run decomposition across consecutive time blocks (`runFrom_add`) identifies the position at time $u$ from the original configuration with the position after $u-T_1$ further steps from the configuration at time $T_1$. Hence the cell belongs to the second visited set.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
