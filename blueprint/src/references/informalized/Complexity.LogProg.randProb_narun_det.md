<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.randProb_narun_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Steps Preserve Run Probability

**Claim.** If the instruction at $l$ is deterministic, then the probability of a configuration property after $N+1$ random choice bits from $(l,v,res)$ equals its probability after the deterministic step followed by $N$ random choice bits.

**Proof.** Condition on the first random bit $c$. Because the instruction at $l$ is deterministic, either value of that bit produces the same next configuration, namely the result of applying the deterministic instruction. The run equation and deterministic-step rule establish this for every remaining choice word (`narun_cons`, `nastep_det`), so the conditional event has the same probability as running the remaining $N$ bits from that next configuration (`randProb_congr`). Averaging over the two equally likely first bits with the one-bit probability decomposition (`randProb_succ`) leaves that same probability unchanged.

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_det`, `Randomized.randProb_congr`, `Randomized.randProb_succ`.
