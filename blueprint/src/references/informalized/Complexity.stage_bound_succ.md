<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_bound_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor stage bound

**Claim.** For every sequence $N$ of finite oracle Turing machines and every $i\in\mathbb{N}$, the bound at stage $i+1$ is the maximum of the fresh length chosen from the stage-$i$ bound and that fresh length raised to the power $i$, plus $i$.

**Proof.** By definition, advancing from stage $i$ to stage $i+1$ assigns the new bound as the maximum of the fresh length and the step-count expression computed from the current stage bound. Reading the bound component of that successor-stage data gives the stated equality directly.
