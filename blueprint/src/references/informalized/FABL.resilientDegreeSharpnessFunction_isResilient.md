<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.resilientDegreeSharpnessFunction_isResilient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resilient sharpness function

**Claim.** For $k<n-1$, the function constructed from the first $k+1$ coordinates and the remaining coordinates is $k$-resilient: its nonempty Fourier coefficients on sets of at most $k$ coordinates vanish, and its mean is zero.

**Proof.** Take the prefix set of the first $k+1$ coordinates. Its size is exactly $k+1$ (`card_resilientSharpnessPrefix`). The decoding of the tail monomial depends only on coordinates outside that prefix (`booleanFunctionF₂Decoding_anfMonomial_dependsOn`), since the tail is the complement of the prefix. The parity-times-complement-dependence criterion then says that multiplying this function by the parity on the prefix produces a $k$-resilient function (`parityTimes_isResilient_of_dependsOn_compl`). The constructed sharpness function is precisely this parity-times function, giving the claim.

**Key facts.** `FABL.card_resilientSharpnessPrefix`, `FABL.booleanFunctionF₂Decoding_anfMonomial_dependsOn`, `FABL.parityTimes_isResilient_of_dependsOn_compl`.
