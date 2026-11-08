<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.natCard_linearThresholdFunction_le_profileCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear threshold profile bound

**Claim.** For every $n\in\mathbb N$, the number of linear threshold functions on $\{-1,1\}^n$ is at most $(2^n+1)^{|\mathcal F_{n,1}|}$, where $\mathcal F_{n,1}$ is the family of subsets of coordinates of size at most one.

**Proof.** Associate to each linear threshold function its low-degree agreement profile, which records, for each set in $\mathcal F_{n,1}$, one of $2^n+1$ possible values. The profile is injective on linear threshold functions (\texttt{lowDegreeAgreementProfile_injective_on_linearThreshold}), so their number is at most the number of such profiles. A function from a finite family of size $|\mathcal F_{n,1}|$ to a set of size $2^n+1$ has $(2^n+1)^{|\mathcal F_{n,1}|}$ possibilities, giving the bound.

**Key facts.** `FABL.lowDegreeAgreementProfile_injective_on_linearThreshold`.
