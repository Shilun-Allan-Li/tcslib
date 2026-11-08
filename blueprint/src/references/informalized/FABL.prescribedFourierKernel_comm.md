<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.prescribedFourierKernel_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the prescribed Fourier kernel

**Claim.** The prescribed Fourier kernel at $(a,x)$ equals its value at $(x,a)$.

**Proof.** Write both kernel values using the explicit kernel formula (`prescribedFourierKernel_apply`). They have the same scalar factor and sum over $S\in\mathcal F$. In each summand, the two real monomial values occur as a product; commutativity of multiplication interchanges their order without changing the term. Thus the sums, and hence the kernel values, agree.

**Key facts.** `FABL.prescribedFourierKernel_apply`.
