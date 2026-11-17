<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAdjoinRootEncode_binaryXMulMod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication by the adjoined root

**Claim.** Encoding the vector obtained by shifting the coefficients of $a$ up one degree and adding its top coefficient times $m$ equals the adjoined root times the encoding of $a$.

**Proof.** The low-coefficient polynomial of the resulting vector is $X$ times the low-coefficient polynomial of $a$, plus the top coefficient of $a$ times the modulus (`binaryLowPolynomial_binaryXMulMod`). Pass this identity to the quotient algebra. The quotient map sends $X$ to the adjoined root, while the modulus itself maps to zero. Thus the second summand vanishes, and the first becomes the adjoined root times the encoding of $a$.

**Key facts.** `FABL.binaryLowPolynomial_binaryXMulMod`.
