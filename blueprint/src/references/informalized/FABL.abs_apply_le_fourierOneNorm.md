<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdFunctions.lean :: FABL.abs_apply_le_fourierOneNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Bound from the Fourier One Norm

**Claim.** At every point of the Boolean cube, the absolute value of a real-valued function is at most the sum of the absolute values of its Fourier coefficients.

**Proof.** Use the Fourier expansion to write $f(x)=\sum_S \widehat f(S)\,\chi_S(x)$ (`FABL.fourier_expansion`). The triangle inequality bounds the absolute value of this sum by $\sum_S |\widehat f(S)\chi_S(x)|$. Each Boolean-cube monomial has square $1$ (`FABL.monomial_sq`), so its absolute value is $1$. Thus each summand's absolute value is $|\widehat f(S)|$, and the resulting sum is exactly the Fourier one norm.

**Key facts.** `FABL.fourier_expansion`, `FABL.monomial_sq`.
