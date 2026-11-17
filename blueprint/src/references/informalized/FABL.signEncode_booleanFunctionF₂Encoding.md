<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Encoding.lean :: FABL.signEncode_booleanFunctionF₂Encoding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a Boolean function's value

**Claim.** The sign encoding of the binary encoding of $f$ at $x$ equals $f$ evaluated at the sign vector corresponding to $x$.

**Proof.** The binary encoding of $f$ at $x$ is defined by applying the inverse of the binary-to-sign equivalence to $f$ at the sign vector corresponding to $x$. Applying the sign encoding, which is the forward map of that equivalence, cancels the inverse and returns that value of $f$.
