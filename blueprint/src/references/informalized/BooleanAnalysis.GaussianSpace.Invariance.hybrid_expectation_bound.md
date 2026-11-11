<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.hybrid_expectation_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hybrid expectation bound

**Claim.** If each consecutive pair of hybrid expectations differs in absolute value by at most its assigned bound $B_i$, then the difference between the all-left and all-right expectations is at most the sum of those bounds.

**Proof.** Define $P(r)=\int_\Omega \psi(\operatorname{evalMultilinearRV}(F,\operatorname{hybridInput}(Z,r),\omega))\,d\mu(\omega)$. The initial-hybrid identity identifies $P(0)$ with the all-left expectation, and the terminal-hybrid identity ($\texttt{hybridInput\_all}$) identifies $P(n)$ with the all-right expectation. The triangle inequality along the sequence $P(0),P(1),\ldots,P(n)$ bounds the distance between its endpoints by the sum of the consecutive distances. Reindex this finite sum by $i\in\mathrm{Fin}(n)$; the assumed bound for step $i$ bounds its corresponding distance by $B_i$. Summing gives the stated estimate.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.hybridInput_zero`, `BooleanAnalysis.GaussianSpace.Invariance.hybridInput_all`.
