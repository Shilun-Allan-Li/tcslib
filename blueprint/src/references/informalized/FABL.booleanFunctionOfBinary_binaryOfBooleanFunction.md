<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.booleanFunctionOfBinary_binaryOfBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a Boolean Function

**Claim.** Transporting a sign-valued Boolean function to the binary cube and back to the sign cube recovers the original function.

**Proof.** Fix a sign input. The conversion back evaluates the binary-cube function at the binary vector corresponding to that sign input. By definition, that function evaluates the original function at the sign vector obtained from this binary vector. The equivalence and its inverse return the original sign input, so the values agree pointwise and hence the functions are equal.
