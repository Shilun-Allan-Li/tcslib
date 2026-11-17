<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddBLRAndAndRejectionValues_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Rejection Values

**Claim.** For every natural number $n$, the set of rejection probabilities of the odd BLR-and-AND tester on non-dictator Boolean functions is nonempty.

**Proof.** There is at least one non-dictator Boolean function in dimension $n$ (`nonDictatorBooleanFunctions_nonempty`). Applying the map that sends each such function to its rejection probability gives a nonempty image, which is exactly the set of rejection values in question.

**Key facts.** `FABL.nonDictatorBooleanFunctions_nonempty`.
