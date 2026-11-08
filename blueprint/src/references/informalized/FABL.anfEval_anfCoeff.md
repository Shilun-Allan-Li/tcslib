<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfEval_anfCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of ANF coefficients

**Claim.** The algebraic normal form formed from the coefficients of $f$ evaluates to $f$ at every input.

**Proof.** Fix a cube point $x$ and let $U$ be its support. The support-to-cube correspondence says that the cube point associated to $U$ is $x$. The evaluation identity on points of the form associated to a subset (`FABL.anfEval_anfCoeff_f₂CubeOfFinset`) says that the coefficient family of $f$ evaluates there to $f$ itself. Applying it to $U$ yields the desired equality at $x$. As $x$ was arbitrary, the functions agree everywhere.

**Key facts.** `FABL.anfEval_anfCoeff_f₂CubeOfFinset`.
