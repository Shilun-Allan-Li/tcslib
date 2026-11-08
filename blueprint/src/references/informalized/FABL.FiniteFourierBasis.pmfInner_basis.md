<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.FiniteFourierBasis.pmfInner_basis -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthonormality in the weighted inner product

**Claim.** For any two basis vectors of a finite Fourier basis, their [?] weighted inner product is $1$ when their indices agree and $0$ otherwise.

**Proof.** By definition, the weighted inner product of two functions is the expectation of their pointwise product. Thus the inner product of the basis vectors indexed by $a$ and $b$ is the weighted expectation of $x\mapsto B_a(x)B_b(x)$. The basis orthonormality condition gives exactly $1$ if $a=b$ and $0$ otherwise.

**Key facts.** `FABL.pmfInner_eq_expect`.
