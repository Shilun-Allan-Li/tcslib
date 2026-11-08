<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/LinearCSPAlgorithms.lean :: FABL.CSPInstance.gaussianEliminationWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Elimination Work Bound

**Claim.** The Gaussian elimination work is at most $m(|V|+1)+|V|m(|V|+2)+|V|(|V|+1)$, where $m$ is the number of constraints counted with multiplicity.

**Proof.** The solver’s work bound gives an upper bound of $|V|\,\ell(|V|+2)+|V|(|V|+1)$ for a row list of length $\ell$ (`cubicF₂LinearSolverBackend_work_le`). The instance’s row list is obtained by converting each constraint in the constraint multiset to a linear equation, so its length is $m$. Substituting this into the solver bound and adding the instance’s initial cost $m(|V|+1)$ yields the stated expression. The remaining rearrangement is arithmetic.

**Key facts.** `FABL.cubicF₂LinearSolverBackend_work_le`.
