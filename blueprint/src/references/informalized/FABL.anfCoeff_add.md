<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.anfCoeff_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of ANF coefficients

**Claim.** For any two functions $f,g:\mathbb F_2^n\to\mathbb F_2$, the coefficient function of their pointwise sum is the pointwise sum of their coefficient functions.

**Proof.** It suffices to show that the two proposed coefficient functions have the same evaluation at every input, since evaluation is injective (`FABL.anfEval_injective`). Evaluating the coefficients of $f+g$ recovers $f+g$ (`FABL.anfEval_anfCoeff`). On the other side, evaluation is additive (`FABL.anfEval_add`), and evaluating the coefficients of $f$ and $g$ separately recovers those functions (`FABL.anfEval_anfCoeff`). The two evaluations therefore agree pointwise, proving the coefficient functions equal.

**Key facts.** `FABL.anfEval_injective`, `FABL.anfEval_anfCoeff`, `FABL.anfEval_add`.
