<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.finiteAddFourierCoeff_zero_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Fourier Coefficient and Expectation

**Claim.** For a finite additive commutative group $G$ and $g:G\to\mathbb{R}$, the Fourier coefficient of $g$ at the trivial character is its uniform average over $G$.

**Proof.** By definition, the Fourier coefficient is the uniform inner product of $g$ with the character. The uniform-inner-product identity for the finite uniform measure rewrites this as an expectation; the trivial character is the constant function $1$, so the inner product reduces to the uniform average of $g$.
