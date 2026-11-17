<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.binaryAdjoinRootEncode_binaryPowMod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Powers under encoding

**Claim.** For a positive length and an irreducible modulus, encoding the vector obtained by raising a vector to the $e$th power modulo the modulus equals the $e$th power of its encoding in the quotient algebra.

**Proof.** Proceed by induction on $e$. For $e=0$, the power vector is the vector of coefficients of $1$, whose low-coefficient polynomial is $1$; its encoding is therefore the multiplicative identity, as required. For the successor step, the power vector is computed by multiplying the preceding power vector by $r$ modulo the modulus. The encoding of modular multiplication is the product of the encodings (`adjoinRoot_mk_binaryMulMod`). By the induction hypothesis, this product is the $e$th power of the encoding of $r$ multiplied by the encoding of $r$. The law $x^e x=x^{e+1}$ finishes the induction.

**Key facts.** `FABL.binaryLowPolynomial_binaryOneCoefficients`, `FABL.adjoinRoot_mk_binaryMulMod`.
