<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorFourierSupport_add_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support of a Sum

**Claim.** For real-valued functions $f,g$ on $\mathbb{F}_2^n$, the vector Fourier support of $f+g$ is contained in the union of the vector Fourier supports of $f$ and $g$.

**Proof.** Take a frequency $\gamma$ in the support of $f+g$. By the characterization of support membership as nonvanishing of the corresponding coefficient (`FABL.mem_vectorFourierSupport`), its coefficient for $f+g$ is nonzero. The coefficient additivity formula (`FABL.vectorFourierCoeff_add`) writes it as the sum of the coefficients for $f$ and $g$. If the coefficient for $f$ is nonzero, then $\gamma$ lies in the support of $f$. If it is zero, the coefficient for $g$ must be nonzero, since otherwise their sum would vanish; hence $\gamma$ lies in the support of $g$. In either case it lies in the union.

**Key facts.** `FABL.mem_vectorFourierSupport`, `FABL.vectorFourierCoeff_add`.
