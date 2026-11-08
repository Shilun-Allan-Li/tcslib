<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.booleanFunctionF₂Decoding_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Form of Binary Decoding

**Claim.** The real-valued version of the decoded sign-valued function equals the real sign encoding of the binary function transported from the binary cube to the sign cube.

**Proof.** Evaluate both functions at an arbitrary sign vector $x$. By definition, the decoded function first transports $x$ back to the binary cube, applies $f$, and encodes the result as a sign. Taking its real value therefore gives the real value of that encoded sign. The right-hand side performs the same inverse transport, applies $f$, and then takes the real value of the sign encoding. These are the same quantity, so the functions agree at every $x$.
