<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.exists_anfCoeff_ne_zero_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero ANF coefficient

**Claim.** If a function $f:\mathbb F_2^n\to\mathbb F_2$ is nonzero, then at least one coefficient in its algebraic normal form is nonzero.

**Proof.** Suppose instead that every ANF coefficient of $f$ vanishes. The reconstruction identity for the algebraic normal form says that evaluating the function reconstructed from these coefficients gives $f$ itself ($\mathrm{anfEval\_anfCoeff}$). With every coefficient zero, that evaluation is the zero function. Hence $f=0$, contradicting the hypothesis that $f$ is nonzero.

**Key facts.** `FABL.anfEval_anfCoeff`.
