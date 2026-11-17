<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.isRelevant_f₂HypothesisBooleanFunction_of_anfCoeff_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero ANF Coefficient Implies Relevance

**Claim.** If an ANF coefficient indexed by $S$ is nonzero and $i\in S$, then the associated sign-valued hypothesis function is relevant at coordinate $i$.

**Proof.** By the characterization of relevance, it is enough to rule out the possibility that changing coordinate $i$ never changes the real-valued function. Suppose there were no witness to relevance. Translating between the binary cube and the sign cube, and using that the two encodings exchange $0,1$ with $1,-1$, shows that the binary function has the same value on the two inputs obtained by setting coordinate $i$ to $0$ and to $1. This holds for every input. The ANF cancellation fact then says that every coefficient indexed by a set containing $i$ vanishes, in particular the coefficient indexed by $S$ (\texttt{FABL.anfCoeff_eq_zero_of_update_eq}), contradicting its assumed nonvanishing.

**Key facts.** `FABL.isRelevant_iff_exists_setCoordinate_ne`, `FABL.binaryCubeSignEquiv_apply`, `FABL.setCoordinate_apply_of_ne`, `FABL.setCoordinate_apply_self`, `FABL.signEncode_one`, `FABL.signEncode_zero`, `FABL.signValue_injective`, `FABL.anfCoeff_eq_zero_of_update_eq`.
