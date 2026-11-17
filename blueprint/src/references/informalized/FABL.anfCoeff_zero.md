<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.anfCoeff_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of the zero function

**Claim.** The algebraic normal form coefficients of the zero function are all zero.

**Proof.** Evaluate both the coefficients of the zero function and the identically zero coefficient family. The evaluation map is injective (`FABL.anfEval_injective`), so it suffices to show these evaluations agree. Every value of the zero function is zero, hence its algebraic normal form evaluates to zero everywhere by the representation identity (`FABL.anfEval_anfCoeff`). The identically zero coefficient family also evaluates to zero, since every summand has zero coefficient. Injectivity therefore identifies the two coefficient families.

**Key facts.** `FABL.anfEval_injective`, `FABL.anfEval_anfCoeff`.
