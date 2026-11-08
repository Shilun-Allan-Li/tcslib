<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.binaryAdjoinRootEncode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the encoding

**Claim.** Encoding length-$\ell$ vectors as their low-coefficient polynomials in the quotient algebra is injective.

**Proof.** Suppose vectors $a$ and $b$ have the same encoding. Their low-coefficient polynomials therefore have the same image in the quotient, so the difference of those polynomials maps to zero. The kernel of the quotient map consists of multiples of the modulus; hence this difference is divisible by the modulus. Each low-coefficient polynomial has degree less than $\ell$ (`binaryLowPolynomial_degree_lt`), so their difference has degree less than $\ell$ as well. The modulus has degree exactly $\ell$ (`binaryMonicPolynomial_degree`). A polynomial of degree strictly below the modulus cannot be a nonzero multiple of it, so the difference is zero. Injectivity of the low-coefficient polynomial representation (`binaryLowPolynomial_injective`) now gives $a=b$.

**Key facts.** `FABL.binaryLowPolynomial_degree_lt`, `FABL.binaryMonicPolynomial_degree`, `FABL.binaryLowPolynomial_injective`.
