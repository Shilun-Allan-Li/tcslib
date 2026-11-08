<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Affine.lean :: FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree-One Functions Are Affine

**Claim.** A function from $\mathbb F_2^n$ to $\mathbb F_2$ with algebraic degree at most one is affine: it has the form $b+a\cdot x$.

**Proof.** Choose the constant coefficient of the algebraic normal form as $b$, and choose the coefficient of the singleton monomial $\{i\}$ as the $i$th coordinate of $a$. The algebraic normal form of this affine function has exactly those constant and singleton coefficients (`anfEval_affineCoefficients`). The original function is recovered by evaluating its algebraic normal form (`anfEval_anfCoeff`), so it suffices to compare coefficients. The empty-set coefficient agrees by the choice of $b$, and each singleton coefficient agrees by the choice of $a$. For any other nonempty set $S$, its size exceeds one. If its coefficient were nonzero, the degree characterization (`algebraicDegree_le_iff`) would force $|S|\le1$, a contradiction. Thus all higher-degree coefficients vanish, and the two algebraic normal forms agree.

**Key facts.** `FABL.anfEval_anfCoeff`, `FABL.anfEval_affineCoefficients`, `FABL.algebraicDegree_le_iff`.
