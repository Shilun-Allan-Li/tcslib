<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.prescribedFourierKernel_apply_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prescribed Fourier kernel on the diagonal

**Claim.** For a nonempty family $\mathcal F$, the prescribed Fourier kernel associated with it takes the value $1$ at every diagonal pair $(a,a)$.

**Proof.** Use the kernel formula to write the diagonal value as $|\mathcal F|^{-1}$ times the sum, over $S\in\mathcal F$, of $\operatorname{monomial}_S(a)^2$. Each such square is $1$ (`monomial_sq`), so the sum has exactly $|\mathcal F|$ terms, all equal to $1$. Since $\mathcal F$ is nonempty, its cardinality is positive and the reciprocal cancels this factor, giving $1$.

**Key facts.** `FABL.prescribedFourierKernel_apply`, `FABL.monomial_sq`.
