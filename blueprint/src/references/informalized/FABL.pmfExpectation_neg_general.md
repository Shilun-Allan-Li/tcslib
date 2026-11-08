<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_neg_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation of expectation

**Claim.** For a probability mass function $\pi$ on a finite set and a real-valued function $f$, the expectation of $-f$ under $\pi$ is the negative of the expectation of $f$.

**Proof.** Regard $-f$ pointwise as the function $x\mapsto (-1)f(x)$. The expectation scales by a constant: $\mathbb E_\pi[cf]=c\mathbb E_\pi[f]$ (`pmfExpectation_const_mul`). Taking $c=-1$ gives the stated identity.

**Key facts.** `FABL.pmfExpectation_const_mul`.
