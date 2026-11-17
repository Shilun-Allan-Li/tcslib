<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean :: Complexity.LogProg.ISGen.gvloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer Enumeration Invariant

**Claim.** Under the stated hypotheses, the machine at the outer-enumeration test terminates within register bound $B$ and accepts exactly when the stated outer recursive condition holds with terminal predicate $\operatorname{Kont}$.

**Proof.** Induct on the number $\sigma.K-\sigma.v$ of outer codes remaining, strengthening the claim to arbitrary states satisfying the same invariants. If no codes remain, the outer test proceeds to the stage-end state, and the assumed continuation applies with the current count. This is precisely the depth-zero case of the outer recursive condition.

With codes remaining, the machine chooses between treating the current code $v$ as a member of the next ball and treating it as a nonmember. On the member branch, it verifies membership and uses the walk-based test `gwalk_spec`; it then queries the acceptance oracle. An accepting code causes rejection, while a nonaccepting code increments the outer count and continues at $v+1$. This realizes the first clause of the outer recursive condition, which requires membership and nonacceptance and increases the count.

On the nonmember branch, the machine clears the inner counters and runs the inner enumeration. By `guloop`, this succeeds exactly when its recursive condition certifies that the current code is outside the next ball and the continuation at $v+1$ succeeds with the unchanged outer count. The inner test supplies exactly the second predicate of the outer recursive condition. The nondeterministic choice therefore represents its two alternatives, and the induction hypothesis handles the remaining outer codes in either case. At the end, the supplied continuation yields $\operatorname{Kont}$ exactly when the terminal count condition holds. Register bounds are preserved by the hypotheses and $K+1\le B$.

**Key facts.** `Complexity.LogProg.ISGen.gwalk_spec`, `Complexity.LogProg.ISGen.guloop`, `Complexity.LogProg.ISCount.gs_and`.
