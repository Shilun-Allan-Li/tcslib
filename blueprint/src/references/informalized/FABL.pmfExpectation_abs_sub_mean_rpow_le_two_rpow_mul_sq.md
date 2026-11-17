<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.pmfExpectation_abs_sub_mean_rpow_le_two_rpow_mul_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign-Valued Moment Bound

**Claim.** For a sign-valued function and every $p\ge1$, the absolute deviation moment of order $p$ is at most $2^p$ times the second moment of the deviation.

**Proof.** Split into the cases $p\le2$ and $p>2$. In the first case, the sharper bound by the second moment is \texttt{pmfExpectation\_abs\_sub\_mean\_rpow\_le\_sq}. The second moment is nonnegative by nonnegativity of expectation (\texttt{pmfExpectation\_nonneg}), and $1\le2^p$ for $p\ge1$, so the stated bound follows. In the second case, the mean of a sign-valued function lies in $[-1,1]$ (\texttt{pmfExpectation\_mem\_Icc\_of\_hasSignRange}); hence each deviation has absolute value at most $2$. The pointwise inequality $|z|^p\le2^p z^2$ for $|z|\le2$ and $p\ge2$ (\texttt{abs\_rpow\_le\_two\_rpow\_mul\_sq}), followed by monotonicity of expectation (\texttt{pmfExpectation\_mono}), bounds the desired expectation by the expectation of $2^p$ times the squared deviation. Pulling out this constant (\texttt{pmfExpectation\_const\_mul}) gives the result.

**Key facts.** `FABL.pmfExpectation_abs_sub_mean_rpow_le_sq`, `FABL.pmfExpectation_nonneg`, `FABL.pmfExpectation_mem_Icc_of_hasSignRange`, `FABL.abs_rpow_le_two_rpow_mul_sq`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const_mul`.
