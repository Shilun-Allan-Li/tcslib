<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentDual.lean :: FABL.IsBent.isSignValued_bentDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Dual Is Sign-Valued

**Claim.** If $f$ is bent, then its dual takes values of absolute value $1$.

**Proof.** Fix an input $\gamma$. The dual value is $2^{\lfloor n/2\rfloor}$ times the corresponding Walsh Fourier coefficient. Its absolute value is therefore $2^{\lfloor n/2\rfloor}$ times the absolute value of that coefficient. Bentness says the latter is $\bigl(2^{\lfloor n/2\rfloor}\bigr)^{-1}$, so the product is $1$.
