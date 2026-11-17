<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.sum_ne_sq_prescribedFourierKernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared mass of the prescribed Fourier kernel

**Claim.** For a nonempty finite family of subsets and any fixed $x$, the sum of the squared prescribed Fourier kernel over all $a\ne x$ equals the cube size divided by the family size, minus $1$.

**Proof.** First sum over every $a$. By symmetry of the kernel in its two sign-vector arguments (\(\texttt{FABL.prescribedFourierKernel_comm}\)), this total equals the sum over $a$ of the squared kernel with $x$ as its first argument. The expected squared kernel at a fixed first argument is $1/|\mathcal F|$ (\(\texttt{FABL.expect_sq_prescribedFourierKernel}\)); on the uniform finite cube, the total sum is therefore the cube cardinality divided by $|\mathcal F|$. Now remove the term $a=x$. The kernel at the diagonal is $1$ (\(\texttt{FABL.prescribedFourierKernel_apply_self}\)), so its squared contribution is $1$. Subtracting this term gives the claimed value.

**Key facts.** `FABL.expect_sq_prescribedFourierKernel`, `FABL.prescribedFourierKernel_comm`, `FABL.prescribedFourierKernel_apply_self`.
