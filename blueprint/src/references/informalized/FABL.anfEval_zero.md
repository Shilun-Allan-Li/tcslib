<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfEval_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero polynomial evaluation

**Claim.** The algebraic normal form with every coefficient equal to zero evaluates to zero at every point of the Boolean cube.

**Proof.** By definition, the evaluation is a sum whose term for each coordinate subset is its coefficient multiplied by the corresponding monomial. Every coefficient is zero, so every summand is zero, and hence the sum is zero.
