<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.constantPairBooleanFunction_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Form of the Constant-Pair Function

**Claim.** The real-valued version of the sign-valued function obtained from the binary constant-pair indicator equals the real sign encoding of that indicator evaluated at the binary vector corresponding to each sign vector.

**Proof.** Apply the general identity that the real form of a function obtained by decoding a binary-valued function is the binary-cube function of its real sign encoding (booleanFunctionF₂Decoding_toReal), taking the binary function to be the constant-pair indicator. Since the constant-pair Boolean function is exactly this decoding, the identity gives the claimed equality.

**Key facts.** `FABL.booleanFunctionF₂Decoding_toReal`.
