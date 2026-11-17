<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.lowDegreeFourierEstimatorProgram_cost_le_workBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost bounded by the work bound

**Claim.** If the low-degree estimator’s work bound is at most $B$, every supported outcome uses at most $B$ random examples, makes no membership queries, and has charged work at most $B$.

**Proof.** The exact-cost result identifies the outcome’s cost as $(R,0,W)$, where $R$ is the learner’s random-example cost and $W$ is its work bound. Thus the query count is zero and the charged work is at most $B$ by the assumed inequality $W\le B$. Also, by definition, $W=R+R(n+1)$, so $R\le W$ since $R(n+1)\ge0$. Combining $R\le W$ with $W\le B$ gives the claimed random-example bound.

**Key facts.** `FABL.lowDegreeFourierEstimatorProgram_cost_eq`.
