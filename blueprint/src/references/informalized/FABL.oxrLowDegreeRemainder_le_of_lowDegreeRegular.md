<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrLowDegreeRemainder_le_of_lowDegreeRegular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Fourier Remainder Bound

**Claim.** If every nonempty set of size at most $t$ has Fourier coefficient of magnitude at most $R$, where $R\ge0$, then the low-degree sum of squared Fourier coefficients weighted by the corresponding absolute random-subset averages is at most $R$.

**Proof.** Rewrite the restricted sum as a sum over all sets, inserting an indicator for the condition $|S|\le t$. For a set meeting that condition, its absolute random-subset Fourier average is at most $R$: when the intersection with a sampled subset is empty, oddness makes that coefficient zero; otherwise the intersection is nonempty, has size at most $t$, and regularity bounds its coefficient by $R$. Multiplying by the nonnegative square of the coefficient preserves this upper bound. For sets outside the cutoff, the inserted term is zero and is at most $R\widehat f(S)^2$ since $R\ge0$. Thus the sum is at most $R\sum_S\widehat f(S)^2$. Parseval’s inequality for a function valued in $[-1,1]$ bounds this total Fourier mass by $1$, so the desired sum is at most $R$.

**Key facts.** `FABL.oxrRandomSubsetAbsFourierAverage_le_of_lowDegreeRegular`, `FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`.
