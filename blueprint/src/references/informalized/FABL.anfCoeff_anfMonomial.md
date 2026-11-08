<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.anfCoeff_anfMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# ANF coefficients of a monomial

**Claim.** For every coordinate set $S$, the coefficient function of the monomial $x\mapsto\prod_{i\in S}x_i$ is $1$ at $S$ and $0$ at every other set.

**Proof.** Evaluate both the actual coefficient function and the proposed function that is $1$ only at $S$. The actual coefficients evaluate to the monomial (`FABL.anfEval_anfCoeff`). In the proposed evaluation, the sole surviving term is the monomial indexed by $S$, so the result is also $\prod_{i\in S}x_i$. Since evaluation is injective (`FABL.anfEval_injective`), the coefficient functions coincide.

**Key facts.** `FABL.anfEval_injective`, `FABL.anfEval_anfCoeff`.
