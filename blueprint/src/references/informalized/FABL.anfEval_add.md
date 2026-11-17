<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfEval_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of polynomial evaluation

**Claim.** Evaluating the coefficientwise sum of two coefficient families gives the sum of their evaluations at every input.

**Proof.** Expand the evaluation as a sum over subsets. Distribute each coefficient sum across multiplication by its monomial, then separate the resulting finite sum into the sum of the terms involving the first coefficient family and the sum of those involving the second. These are precisely the two evaluations, so their sum is the claimed value.
