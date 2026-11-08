<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.arcsinOddPowerCoefficient_mul_two_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Arcsine Coefficient Formula

**Claim.** For every natural number $j$, the coefficient of the arcsine power series indexed by $2j+1$ equals $\binom{2j}{j}/\bigl(2^{2j}(2j+1)\bigr).

**Proof.** The coefficient identity is already known when the odd exponent is written as $2j+1$ (`arcsinOddPowerCoefficient_two_mul_add_one`). Since $j\cdot 2+1=2j+1$, commutativity of multiplication makes that result exactly the stated formula.

**Key facts.** `FABL.arcsinOddPowerCoefficient_two_mul_add_one`.
