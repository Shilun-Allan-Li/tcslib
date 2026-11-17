<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddBLREquationFunctionTester_eq_oddBLRAcceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Two Tester Probabilities

**Claim.** For every Boolean function, the acceptance probability of the equation tester equals the odd BLR acceptance probability of its associated bounded real-valued function.

**Proof.** First express the equation tester’s acceptance probability as the uniform average of the indicator that $f(x)f(y)f(bxy)=b$ (`oddBLREquationFunctionTester_acceptanceProbability`). The odd BLR acceptance formula (`hastadAcceptanceProbability_eq_expect`) expresses the other tester’s probability as the same average, with integrand $(1+	ext{signValue}(b)	ilde f(x)	ilde f(y)	ilde f(bxy))/2$, where $	ilde f$ is the real-valued function associated to the bounded-cube function. At noise parameter zero, the noise operator is the identity (`noiseOperator_one_apply_amplification`), so the noise term in that formula is just $	ilde f(bxy)$. For signs $a,b,c$ and right-hand side $r$, the equation indicator equals $(1+	ext{signValue}(r)	ext{signValue}(a)	ext{signValue}(b)	ext{signValue}(c))/2$ (`signEquation_indicator`). Applying this identity to the three function values makes the two integrands equal pointwise. The associated bounded function has real values equal to the sign values of $f$, so the integrands agree, and hence so do their uniform averages.

**Key facts.** `FABL.oddBLREquationFunctionTester_acceptanceProbability`, `FABL.hastadAcceptanceProbability_eq_expect`, `FABL.noiseOperator_one_apply_amplification`, `FABL.signEquation_indicator`.
