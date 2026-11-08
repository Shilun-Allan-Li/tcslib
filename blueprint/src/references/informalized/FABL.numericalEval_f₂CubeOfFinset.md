<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.numericalEval_f₂CubeOfFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation at a subset indicator

**Claim.** Evaluating a numerical polynomial at the binary vector that is $1$ exactly on $U$ gives the sum of its coefficients over all subsets of $U$.

**Proof.** At the indicator vector of $U$, the numerical monomial indexed by $S$ equals $1$ when $S\subseteq U$ and equals $0$ otherwise (`numericalMonomial_f₂CubeOfFinset`). Consequently, the full evaluation sum keeps exactly the terms with $S\subseteq U$. Rewriting this restricted sum over the powerset of $U$ gives the asserted formula.

**Key facts.** `FABL.numericalMonomial_f₂CubeOfFinset`.
