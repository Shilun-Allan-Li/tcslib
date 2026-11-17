<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticLinearPCPPSystem_isPCPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A linear PCPP for the complete quadratic condition

**Claim.** The specified three-query verifier is a PCPP for the complete quadratic condition, with rejection rate $1/12$.

**Proof.** The proof first establishes that the rate is positive. For completeness, take a word satisfying the quadratic condition and use its designated linear proof. Every verifier check then holds (`completeQuadraticLinearProof_checks`), so no seed rejects. The rejection-probability identity in terms of the uniform distribution on checks (`completeQuadraticLinearPCPPSystem_rejectionProbability`) therefore gives acceptance probability $1$.

For soundness, suppose a word is $\varepsilon$-far from every satisfying word, with $0\le\varepsilon\le1$, and fix any proof. The word itself cannot satisfy the condition: otherwise its distance from itself would be zero, contradicting the assumed farness. Hence some verifier check fails; if all checks held, the converse theorem would imply that the word satisfies the condition (`isCompleteQuadraticOne_of_linearChecks`). A failed check contributes at least $1/(3n+3)$ to the rejection probability (`one_div_checkCount_le_completeQuadratic_failedCheckProbability`).

It remains to bound the claimed rate times $\varepsilon$ by this amount. If $n\ge2$, the repair construction supplies a satisfying word within relative Hamming distance at most $2/n$ (`completeQuadraticFlipNeighbor_isCompleteQuadraticOne`, `relativeHammingDist_completeQuadraticFlipNeighbor_le_two_div`). Farness therefore implies $\varepsilon<2/n$. Together with $n\ge2$ and $\varepsilon\le1$, this yields $\varepsilon/12<1/(3n+3)$. If $n<2$, the assumed nonzero dimension forces $n=1$, and $0\le\varepsilon\le1$ directly gives the same strict inequality. Combining this estimate with the failed-check lower bound proves that rejection probability is strictly greater than $\varepsilon/12$.

**Key facts.** `FABL.completeQuadraticLinearProof_checks`, `FABL.completeQuadraticLinearPCPPSystem_rejectionProbability`, `FABL.isCompleteQuadraticOne_of_linearChecks`, `FABL.completeQuadraticFlipNeighbor_isCompleteQuadraticOne`, `FABL.relativeHammingDist_completeQuadraticFlipNeighbor_le_two_div`, `FABL.one_div_checkCount_le_completeQuadratic_failedCheckProbability`.
