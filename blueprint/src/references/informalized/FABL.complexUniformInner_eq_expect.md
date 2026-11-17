<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.complexUniformInner_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complex Uniform Inner Product as Expectation

**Claim.** For complex-valued functions on a finite type, their uniform inner product equals the uniform expectation of the pointwise product of the complex conjugate of the first function and the second.

**Proof.** The complex uniform inner product with uniform weight is the uniform average of the pointwise inner product (`RCLike.wInner_cWeight_eq_expect`). For complex scalars, the inner product at each point is the conjugate of the first value times the second value. Hence the integrand in that average is exactly $\overline{f(x)}g(x)$, so the claimed expectation identity follows.
