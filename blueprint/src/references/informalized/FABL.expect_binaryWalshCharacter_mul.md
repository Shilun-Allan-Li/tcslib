<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ProbabilityDensitiesAndConvolution.lean :: FABL.expect_binaryWalshCharacter_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality of Walsh characters

**Claim.** The uniform average of the product of the Walsh characters indexed by $S$ and $T$ is $1$ if $S=T$, and $0$ otherwise.

**Proof.** The inner product of two additive characters under the uniform measure on a finite group is $1$ when the characters agree and $0$ otherwise. Apply this orthogonality fact to $\chi_S$ and $\chi_T$: their inner product is the average of their pointwise product, since these real-valued characters take values in $\{\pm1\}$. The characters agree exactly when their indexing sets agree, by injectivity of the Walsh-character map (`binaryWalshCharacter_injective`). Thus the average has the stated value.

**Key facts.** `FABL.binaryWalshCharacter_injective`.
