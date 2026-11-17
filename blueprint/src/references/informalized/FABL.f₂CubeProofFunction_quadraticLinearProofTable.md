<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.f₂CubeProofFunction_quadraticLinearProofTable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding of the Proof Table

**Claim.** For every Boolean proof table, the sign-valued function obtained by restricting it to its first $2^n$ indices and converting to signs equals pointwise the sign encoding of the corresponding binary-valued function.

**Proof.** Fix a point of the binary cube and evaluate both functions there. Each uses the same cube index and the same restriction of the proof table. The left side converts the resulting Boolean value directly to a sign; the right side first converts it to a binary field value and then applies sign encoding. These conversions agree by the Boolean-to-sign identity (`FABL.pcppBoolSignEquiv_eq_signEncode`). Thus the values agree at every point, proving equality of the functions.

**Key facts.** `FABL.pcppBoolSignEquiv_eq_signEncode`.
