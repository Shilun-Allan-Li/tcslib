<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.findIrreducibleBinaryModulus?_isSome -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of an Irreducible Binary Modulus

**Claim.** For every positive natural number $\ell$, the search over binary coefficient vectors of length $\ell$ returns a value.

**Proof.** For positive $\ell$, there exists an irreducible monic binary polynomial of degree $\ell$; represent its coefficients by a vector $m$ of length $\ell$ (`exists_irreducible_binaryMonicPolynomial`). Every such binary vector occurs in the enumerated list (`mem_allBinaryVectors`). The irreducibility criterion for the binary test says that this $m$ passes the test (`binaryMonicIrreducibleTest_eq_true_iff`). Thus the list contains a passing vector, and the characterization of when `find?` returns a value gives the claimed nonemptiness.

**Key facts.** `FABL.exists_irreducible_binaryMonicPolynomial`, `FABL.mem_allBinaryVectors`, `FABL.binaryMonicIrreducibleTest_eq_true_iff`.
