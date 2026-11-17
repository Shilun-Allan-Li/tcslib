<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.numericalCoeff_eq_value_sub_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient from the Top-Cube Value

**Claim.** For any real-valued function on the binary cube, its numerical coefficient at $S$ equals its value at the indicator of $S$ minus the sum of its coefficients over the proper subsets of $S$.

**Proof.** Evaluate the numerical expansion of the function at the indicator point of $S$. The evaluation formula at an indicator point says this value is the sum of the coefficients indexed by all subsets of $S$ (`FABL.numericalEval_f₂CubeOfFinset`), while the coefficient function's expansion equals the original function (`FABL.numericalEval_numericalCoeff`). Separate the term indexed by $S$ from the finite sum; since $S\subseteq S$, this term is present. Rearranging gives the stated coefficient as the function value minus the sum over the remaining subsets.

**Key facts.** `FABL.numericalEval_numericalCoeff`, `FABL.numericalEval_f₂CubeOfFinset`.

**Caveat.** The supplied informal statement describes a different, two-part problem. This account follows the formal statement and proof source, which establish the coefficient recurrence.
