<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAdjoinRootEncode_binaryAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition Under Polynomial Encoding

**Claim.** Encoding the coordinatewise sum of two vectors as a root of the monic polynomial determined by a third vector gives the sum of their individual encodings in the corresponding quotient algebra.

**Proof.** The encoded vector is represented by the image, in the quotient algebra, of its low-degree polynomial. The low-polynomial addition identity (`FABL.binaryLowPolynomial_binaryAdd`) says that the polynomial for the coordinatewise sum is the sum of the two low polynomials. The quotient-algebra map preserves addition, so the image of that polynomial sum is the sum of the two encoded elements. This is the required identity.

**Key facts.** `FABL.binaryLowPolynomial_binaryAdd`.
