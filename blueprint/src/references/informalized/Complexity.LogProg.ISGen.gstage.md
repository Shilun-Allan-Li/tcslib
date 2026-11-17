<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean :: Complexity.LogProg.ISGen.gstage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage Enumeration Invariant

**Claim.** Under the stated hypotheses, the machine at the stage head terminates within register bound $B$ and accepts exactly when $Q$ holds and no code in any ball with radius strictly between $\sigma.i$ and $\sigma.K$ is accepted by the oracle.

**Proof.** Induct on the remaining stage distance $\sigma.K-\sigma.i$, strengthening the claim to allow any state satisfying the same bounds and invariants. If the distance is zero, then $\sigma.i=\sigma.K$, so the stage-head comparison proceeds directly to the comparison stage. The assumed comparison-stage result, applied with the current outer registers and the ball-size register, gives termination and acceptance exactly when $Q$ holds. There are no intermediate radii to check, so this is the desired condition.

For a positive distance, the machine clears the outer registers and enumerates the codes $t<K$. At each such code, it nondeterministically either checks that $t$ is outside the next ball or checks the walk-based nonacceptance condition for $t$. The fact that $t$ is outside the next ball precisely when every code in the current ball is distinct from $t$ and has no $R$-edge to $t$ is `not_mem_succ_iff`. The inner enumeration verifies that condition: `gs_inner` says its recursive count test succeeds exactly when every member of the current ball meets those two requirements. Thus each successful branch certifies that $t$ is not in the next ball. The outer enumeration and its count are summarized by `gs_outer`: together they establish that every member of the next ball is not accepted, and that the final count equals the size of that ball.

At the stage end, the machine copies this count into the ball-size register, advances both stage counters by one, and invokes the induction hypothesis. The count identity supplied by `gs_outer` is exactly the ball-size invariant required at the next stage. The induction hypothesis therefore handles all remaining radii and the assumed comparison-stage computation handles $Q$. Combining the newly verified radius with those later conditions gives the required result. Register bounds for the machine transitions follow from the given bounds and $K+1\le B$.

**Key facts.** `Complexity.LogProg.ISCount.not_mem_succ_iff`, `Complexity.LogProg.ISCount.gs_inner`, `Complexity.LogProg.ISCount.gs_outer`, `Complexity.LogProg.ISGen.gvloop`.
