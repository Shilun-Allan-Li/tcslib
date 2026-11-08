<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorFourierSupport_const_mul_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support under Scalar Multiplication

**Claim.** For any real number $c$ and real-valued function $f$ on $\mathbb{F}_2^n$, the vector Fourier support of $x\mapsto c f(x)$ is contained in the vector Fourier support of $f$.

**Proof.** Let $\gamma$ lie in the support of $x\mapsto c f(x)$, so its Fourier coefficient there is nonzero by the support-membership characterization (`FABL.mem_vectorFourierSupport`). The coefficient scaling formula (`FABL.vectorFourierCoeff_const_mul`) says this coefficient is $c$ times the coefficient of $f$ at $\gamma$. If the latter coefficient were zero, their product would be zero, contradicting the assumed nonvanishing. Thus $\gamma$ lies in the support of $f$.

**Key facts.** `FABL.mem_vectorFourierSupport`, `FABL.vectorFourierCoeff_const_mul`.
