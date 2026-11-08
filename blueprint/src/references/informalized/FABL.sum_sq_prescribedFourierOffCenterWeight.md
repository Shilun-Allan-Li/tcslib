<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.sum_sq_prescribedFourierOffCenterWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Off-Center Kernel Squared Sum

**Claim.** For a nonempty family of coordinate subsets and a fixed sign vector $x$, the sum over all sign vectors $a$ other than $x$ of the squared prescribed Fourier kernel at $(a,x)$ equals the cube's cardinality divided by the family's cardinality, minus $1$.

**Proof.** In the sum over all sign vectors, the summand is zero when $a=x$ and is the squared kernel otherwise. Filtering the sum to the points with $a\ne x$ therefore leaves exactly the same contributions. The resulting off-center sum is the claimed quantity by the identity for the sum of squared prescribed Fourier kernels away from $x$ (FABL.sum_ne_sq_prescribedFourierKernel).

**Key facts.** `FABL.sum_ne_sq_prescribedFourierKernel`.
