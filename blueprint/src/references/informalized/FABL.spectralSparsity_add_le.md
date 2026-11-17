<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.spectralSparsity_add_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subadditivity of Spectral Sparsity

**Claim.** For real-valued functions $f$ and $g$ on the $n$-dimensional vector space over $\mathbb F_2$, the spectral sparsity of their sum is at most the sum of their spectral sparsities.

**Proof.** The spectral sparsity of a function is the cardinality of its vector Fourier support. By the support inclusion for sums (FABL.vectorFourierSupport_add_subset), every frequency with a nonzero Fourier coefficient of $f+g$ lies in the support of $f$ or the support of $g$: if both coefficients vanished, linearity of the Fourier coefficient would make the coefficient of the sum vanish as well. Thus the support of $f+g$ is contained in the union of the two supports. Its cardinality is at most the cardinality of that union, which is at most the sum of the two support cardinalities. Replacing each support cardinality by its spectral sparsity (FABL.spectralSparsity_eq_card_vectorFourierSupport) yields the claimed inequality.

**Key facts.** `FABL.spectralSparsity_eq_card_vectorFourierSupport`, `FABL.vectorFourierSupport_add_subset`.
