<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean :: Complexity.LogProg.ISGen.noAcc_balls_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Accepting Codes in Bounded Balls

**Claim.** Under the stated bound on $K$, every positive-radius ball of radius at most $K$ contains no accepting code exactly when no reachable code is accepting.

**Proof.** The code bound makes $K$ positive. If every ball of positive radius at most $K$ contains no accepting code, use the ball of radius $K$: membership there is equivalent to reachability by `mem_ball_iff_rcode`, giving the desired assertion for every reachable code. Conversely, suppose no reachable code is accepting. For any $0<j\le K$, inclusion of the radius-$j$ ball in the radius-$K$ ball follows from monotonicity (`Complexity.LogProg.ISCount.ball_mono`). A code in the smaller ball is therefore in the radius-$K$ ball, hence reachable by `mem_ball_iff_rcode`, and so cannot be accepting.

**Key facts.** `Complexity.LogProg.ISCount.ball_mono`, `Complexity.LogProg.ISGen.mem_ball_iff_rcode`.
