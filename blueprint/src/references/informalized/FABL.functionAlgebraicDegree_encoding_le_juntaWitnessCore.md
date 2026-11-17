<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.functionAlgebraicDegree_encoding_le_juntaWitnessCore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree under junta restriction

**Claim.** If a Boolean function depends only on coordinates in $J$, then its algebraic degree is at most the degree of its restriction obtained by fixing coordinates outside $J$ to $+1$.

**Proof.** The dependence hypothesis identifies the binary encoding of the original function with the function obtained by pulling back the encoded junta witness core along the coordinate embedding of $J$ into the full coordinate set. The degree of a coordinate pullback cannot exceed the degree of the function being pulled back (`functionAlgebraicDegree_coordinatePullback_le`). Applying this bound to the encoded core gives the stated inequality.

**Key facts.** `FABL.booleanFunctionF₂Encoding_eq_juntaWitnessCore_pullback`, `FABL.functionAlgebraicDegree_coordinatePullback_le`.
