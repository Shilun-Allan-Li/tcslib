<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.spectralSparsity_const_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral Sparsity under Scalar Multiplication

**Claim.** For real $c$ and a real-valued function $f$ on the $n$-dimensional vector space over $\mathbb F_2$, the spectral sparsity of $x\mapsto c f(x)$ is at most that of $f$.

**Proof.** The spectral sparsity of a function is the cardinality of its vector Fourier support (FABL.spectralSparsity_eq_card_vectorFourierSupport). The support inclusion for scalar multiples (FABL.vectorFourierSupport_const_mul_subset) says that any frequency with a nonzero coefficient of $x\mapsto c f(x)$ must already have a nonzero coefficient of $f$. Indeed, the Fourier coefficient scales by $c$, so it cannot become nonzero if the original coefficient was zero. Taking cardinalities of the included finite supports proves the inequality.

**Key facts.** `FABL.spectralSparsity_eq_card_vectorFourierSupport`, `FABL.vectorFourierSupport_const_mul_subset`.
