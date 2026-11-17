<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.firstNonconstantLowDegreeMonomial_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the selected monomial

**Claim.** If the coefficient support contains no nonconstant monomial, the represented polynomial is the constant given by its empty-monomial coefficient. Otherwise, the selected nonconstant monomial yields positive influence in its least coordinate after sign encoding.

**Proof.** Let the support consist of the nonconstant monomials whose coefficients are nonzero, and split according to whether this support is empty. If it is nonempty, the construction selects an element of the support and therefore produces a nonempty monomial $S$ with nonzero coefficient. Its least coordinate belongs to $S$. The coefficient of $S$ in the algebraic normal form of the evaluated polynomial is its extended coefficient (`anfCoeff_lowDegreeF₂Eval`), hence is nonzero. The criterion that a nonzero algebraic-normal-form coefficient makes each coordinate in that monomial relevant (`isRelevant_f₂HypothesisBooleanFunction_of_anfCoeff_ne_zero`) now gives positive influence in the selected least coordinate. If the support is empty, every nonconstant coefficient vanishes, so the polynomial is the constant function given by the empty-monomial coefficient (`lowDegreeF₂Eval_eq_const_of_nonconstantSupport_empty`). These two cases give the asserted alternatives.

**Key facts.** `FABL.anfCoeff_lowDegreeF₂Eval`, `FABL.isRelevant_f₂HypothesisBooleanFunction_of_anfCoeff_ne_zero`, `FABL.lowDegreeF₂Eval_eq_const_of_nonconstantSupport_empty`.
