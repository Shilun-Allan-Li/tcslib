<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.uniformProbability_clauseEval_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform probability of a false clause

**Claim.** For every term on the sign cube, the uniform probability that its clause evaluation is $1$ equals $2^{-w}$, where $w$ is the number of literals in the term.

**Proof.** Negating every coordinate is a bijection of the sign cube, so changing variables by this map preserves uniform probability. Under this change, the event that the clause evaluates to $1$ is equivalent to the event that the corresponding term evaluates to $-1$ (`FABL.CNFFormula.clauseEval_neg_iff_termEval`). The probability of the latter event is $2^{-w}$ by the uniform-probability formula for a DNF term (`FABL.uniformProbability_DNFTerm_eval_neg_one`).

**Key facts.** `FABL.CNFFormula.clauseEval_neg_iff_termEval`, `FABL.uniformProbability_DNFTerm_eval_neg_one`.
