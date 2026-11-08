<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.narun_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step unfolding of a run

**Claim.** Running on a choice string formed by placing $b$ before $\sigma$ is the same as taking the step determined by $b$ and then running on $\sigma$.

**Proof.** This follows directly by unfolding the recursive definition of a run on a nonempty choice string: its first choice $b$ updates the configuration once, after which the remaining string $\sigma$ is run from that updated configuration.
