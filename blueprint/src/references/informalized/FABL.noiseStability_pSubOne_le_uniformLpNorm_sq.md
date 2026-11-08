<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.noiseStability_pSubOne_le_uniformLpNorm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# General Hypercontractive Noise Stability Bound

**Claim.** If $1\le p\le2$, then the uniform inner product of $f$ with its noise-operator image at parameter $p-1$ is at most $\|f\|_p^2$.

**Proof.** The hypotheses imply $p-1\in[0,1]$. Apply the two-function hypercontractivity theorem with both function exponents and the correlation parameter equal to $p-1$, and with both functions equal to $f$. The correlation constraint holds with equality because $\sqrt{(p-1)(p-1)}=p-1$. The theorem bounds the correlated-pair expectation by $\|f\|_{1+(p-1)}^2=\|f\|_p^2$. The correlated-pair expectation equals the uniform inner product of $f$ with its noise-operator image at the same parameter (`correlatedPairExpectation_eq_uniformInner_noiseOperator`), giving the claim.

**Key facts.** `FABL.weakTwoFunctionHypercontractivity_signCube`, `FABL.correlatedPairExpectation_eq_uniformInner_noiseOperator`.
