<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.rstep_noncall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordinary Step at a Non-Call State

**Claim.** If $c$ is in state $l$ and $P$ has no oracle call at $l$, then the register-program step from $c$ equals the ordinary machine step of $P$ from $c$.

**Proof.** Since the state of $c$ is $l$ and the call specification at $l$ is absent, the definition of the register-program step takes its ordinary-machine branch. Thus its result is exactly the ordinary machine step from $c$.
