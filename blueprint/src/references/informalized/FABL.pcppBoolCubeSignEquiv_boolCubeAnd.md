<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.pcppBoolCubeSignEquiv_boolCubeAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Coordinatewise Boolean Conjunction

**Claim.** For any two Boolean vectors of length $n$, encoding their coordinatewise conjunction as a sign vector equals the coordinatewise sign operation on their encodings.

**Proof.** Two vectors of functions are equal when their values agree at each coordinate. Fix a coordinate and apply the Boolean-to-sign conjunction identity, which says that encoding the conjunction of the two Boolean values equals the sign operation on their separate encodings (`FABL.pcppBoolSignEquiv_boolAnd`). This proves equality at every coordinate, hence equality of the vectors.

**Key facts.** `FABL.pcppBoolSignEquiv_boolAnd`.
