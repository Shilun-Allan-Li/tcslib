<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Host Configuration

**Claim.** The host's initial configuration on $x$ is the loader configuration in state $0$, with input head at position $1$, empty assembly buffer, and assembly head at cell $0$.

**Proof.** Both configurations have the host in state $0$, input head at $1$, and empty output. On the scheduler and verifier tape blocks, both tapes are blank and their heads are at cell $0$. On the assembly block, the loader's empty buffer is blank at every cell and its head is also at $0$. Thus all configuration components agree.
