<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.clr_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Across a Cleared Register

**Claim.** If clearing register $r$ at state $l$ leads to $l'$, then bounded reachability from the configuration with $r$ set to zero implies bounded reachability from state $l$ with the original registers, memory, and head position.

**Proof.** The instruction at $l$ is exactly the deterministic clear instruction. Its one-step execution sends the register vector to the vector obtained by updating register $r$ to zero, leaves the memory and head position unchanged, and transfers control to $l'$. The general single-step reachability principle for deterministic instructions (\texttt{step_of}), applied with the register bound and head-position bounds, prefixes this step to the assumed reachability from the cleared configuration.

**Key facts.** `Complexity.LogProg.ExpBFS.step_of`.
