<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecord_replay_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay budget inequality

**Claim.** Under the two assumed bounds on $a$ and $R$, the stated upper bound on $a+2R+4$ follows.

**Proof.** Add the assumed bounds for $a$ and $2R+4$. The second hypothesis gives $2R\le 4l(T+1)^2$. Hence the sum is at most $2n+8+k(3W+7)+((4l+7)+4l)(T+1)^2$, which is the claimed right-hand side after combining coefficients.
