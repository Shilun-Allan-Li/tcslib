<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.pmfExpectation_two_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of Expectation

**Claim.** For a finite set with probability mass function $\pi$, real scalars $a,b$, and functions $f,g$, the expectation of $af+bg$ is $a$ times the expectation of $f$ plus $b$ times the expectation of $g$.

**Proof.** Write $af+bg$ as the sum of the functions $af$ and $bg$. Expectation is additive on sums of functions (`pmfExpectation_add_fun`), and pulling a scalar out of an expectation gives $\mathbb E_\pi[cf]=c\mathbb E_\pi[f]$ (`pmfExpectation_const_mul`). Applying the latter fact to each summand gives the stated formula.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const_mul`.
