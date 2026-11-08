<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAdjoinRootEncode_binaryScaleAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scale-and-add under encoding

**Claim.** Encoding the vector obtained by adding $b$ times $u$ to $v$ equals the encoding of $v$ plus $b$ times the encoding of $u$ in the quotient algebra.

**Proof.** The low-coefficient polynomial of the scale-and-add vector is the sum of the low-coefficient polynomial of $v$ and $b$ times that of $u$ (`binaryLowPolynomial_binaryScaleAdd`). The quotient map from polynomials to the algebra obtained by adjoining a root preserves addition and multiplication, and sends a constant polynomial with value $b$ to the scalar $b$. Applying this map to the polynomial identity gives the claimed equality of encodings.

**Key facts.** `FABL.binaryLowPolynomial_binaryScaleAdd`.
