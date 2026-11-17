<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂PolynomialLearnerWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound on learner work

**Claim.** For any $n,\ell,m$ and any $m$ labeled examples, the learner’s work is at most $m(N+1)+Nm(N+2)+N(N+1)$, where $N$ is the number of subsets of $\{1,\ldots,n\}$ of size at most $\ell$.

**Proof.** Let the rows be the sample equations, let the coordinates be the low-degree monomials, and let the elimination result have work $W$ and pivot count $P$. The elimination work bound (`eliminateF₂Rows_work_le`) gives $W\leq N m(N+2)$: there are $N$ coordinates, $m$ sample rows, and the coordinate count is $N$. The pivot bound (`eliminateF₂Rows_pivots_length_le`) gives $P\leq N$. The learner’s work is $m(N+1)+W+P(N+1)$. Substituting these two inequalities and using monotonicity of addition and multiplication on natural numbers yields the stated bound.

**Key facts.** `FABL.eliminateF₂Rows_work_le`, `FABL.eliminateF₂Rows_pivots_length_le`.
