<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeF₂Eval_eq_const_of_nonconstantSupport_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Evaluation from Empty Support

**Claim.** If a low-degree coefficient family has no nonzero coefficient on any nonempty subset, its evaluation is the constant function given by the coefficient of the empty set.

**Proof.** Fix an input and separate the term indexed by the empty set from the sum. Every other indexing subset is nonempty. If any such subset had a nonzero coefficient, it would belong to the nonconstant support, contradicting the assumption that this support is empty. Thus every other summand vanishes, leaving only the empty-set term. Its monomial is the empty product, equal to $1$, so the evaluation is the coefficient of the empty set, independent of the input.
