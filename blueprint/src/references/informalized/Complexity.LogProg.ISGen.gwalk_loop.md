<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean :: Complexity.LogProg.ISGen.gwalk_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Walk-Loop Invariant

**Claim.** Under the stated hypotheses, the machine at the walk-loop stage terminates within register bound $B$ and accepts exactly when there is an $R$-walk of at most $q(b)-\sigma.stp$ steps from $\sigma.cur$ to $w(b)$ and $Q$ holds.

**Proof.** Induct on the remaining step allowance $\sigma.wb(b)-\sigma.stp$. If it is zero and the current vertex equals the target, the machine clears its scratch registers and continues to the assumed walk-initialization computation; the walk condition is then witnessed by the length-zero walk. If the vertices differ, the machine checks that the step counter has reached its bound and rejects, matching the failure of the zero-step walk condition.

For a positive allowance, first consider the case where the current vertex is already the target. The machine again clears its scratch registers and invokes the continuation, and the walk condition holds by the zero-length alternative in `WalkLe`. Otherwise it rejects if the step counter has already reached its bound. When steps remain, it guesses a next vertex below $K$, checks the edge from the current vertex to that vertex, copies the guessed vertex into the current-vertex register, and increments the step counter. A successful edge query supplies one step of the walk. The induction hypothesis then tests whether the remaining walk reaches the target within the reduced allowance; the assumed continuation supplies $Q$ when that walk exists. Conversely, the recursive definition of `WalkLe` says any nontrivial bounded walk begins with exactly such an edge and has a shorter remaining walk, so the guessed branch captures every witness. This proves the stated equivalence, with termination and register bounds maintained by the hypotheses.

**Key facts.** `Complexity.LogProg.ISCount.St.toV_cur`, `Complexity.LogProg.ISCount.St.toV_wT`, `Complexity.LogProg.ISCount.St.toV_stp`, `Complexity.LogProg.ISCount.toV_wB`, `Complexity.LogProg.ISCount.St.toV_K`, `Complexity.LogProg.ISGen.gwalk_loop`.
