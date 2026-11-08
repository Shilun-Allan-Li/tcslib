<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the constant-one function

**Claim.** The constant-one function on the Boolean cube has algebraic degree $0$.

**Proof.** The algebraic normal form of the constant-one function has coefficient $1$ on the empty set and coefficient $0$ on every nonempty set. Indeed, evaluating its algebraic normal form gives the constant-one function (`anfEval_anfCoeff`), and evaluation is injective on coefficient families (`anfEval_injective`); the stated coefficients evaluate to the constant-one function. Thus the only supported monomial is the empty-set monomial, whose size is zero, so the algebraic degree is $0$.

**Key facts.** `FABL.anfEval_anfCoeff`, `FABL.anfEval_injective`.
