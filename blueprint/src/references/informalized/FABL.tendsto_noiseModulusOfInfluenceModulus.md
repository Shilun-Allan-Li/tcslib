<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.tendsto_noiseModulusOfInfluenceModulus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the induced modulus

**Claim.** The function that assigns the influence modulus at the reciprocal-floor scale tends to zero as the positive noise parameter tends to zero.

**Proof.** By the inverse-floor limit theorem, the integer scale selected by a positive noise parameter tends to infinity as the parameter tends to zero (\(\texttt{tendsto\_inverseNoiseFloorAtZero}\)). Composing this scale with the assumed convergence \(\eta(n)\to0\) shows that the values \(\eta(\lfloor1/\delta\rfloor)\) tend to zero. On the punctured neighborhood in question, the parameter is positive, so the definition of the induced modulus agrees with these values. Thus the two functions agree eventually in the relevant filter, and the desired limit follows.

**Key facts.** `FABL.tendsto_inverseNoiseFloorAtZero`.
