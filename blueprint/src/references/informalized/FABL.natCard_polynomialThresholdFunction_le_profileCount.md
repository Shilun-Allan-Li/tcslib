<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.natCard_polynomialThresholdFunction_le_profileCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial threshold profile bound

**Claim.** For natural numbers $n$ and $k$, the number of Boolean functions on $n$ coordinates admitting a polynomial threshold representation of Fourier degree at most $k$ is at most $(2^n+1)^{|\mathcal F_{n,k}|}$, where $\mathcal F_{n,k}$ consists of coordinate subsets of size at most $k$.

**Proof.** Assign to each such polynomial threshold function its low-degree agreement profile, with one entry for each set in $\mathcal F_{n,k}$. This profile is injective on the functions under consideration (\texttt{lowDegreeAgreementProfile_injective_on_polynomialThreshold}). Therefore their number is bounded by the number of possible profiles. Each entry has $2^n+1$ possibilities, and there are $|\mathcal F_{n,k}|$ entries, so the number of profiles is $(2^n+1)^{|\mathcal F_{n,k}|}$.

**Key facts.** `FABL.lowDegreeAgreementProfile_injective_on_polynomialThreshold`.
