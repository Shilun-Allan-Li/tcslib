<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.arcsinOddPowerCoefficient_two_mul_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Power Coefficient Identity

**Claim.** For every natural number $j$, the coefficient assigned to the exponent $2j+1$ equals the arcsine series coefficient with index $j$.

**Proof.** The exponent $2j+1$ is odd, so the coefficient definition uses its nonzero branch. Subtracting one from the exponent gives $2j$, and halving this gives $j$. Substituting these identities into that branch yields $2/((2j+1)2^{2j+1})\binom{2j}{j}$. Since $2/2^{2j+1}=1/2^{2j}$, this is $\binom{2j}{j}/(2^{2j}(2j+1))$, the arcsine series coefficient of index $j$.
