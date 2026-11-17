<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.levelThreeFactorialConstant_isTheta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial constant growth order

**Claim.** As $d$ tends to infinity through the natural numbers, $\frac{(3d)!^2}{(d!)^6}$ is of the same asymptotic order as $\frac{3^{6d}}{d^2}$; their ratio is eventually bounded above and below by positive constants.

**Proof.** The preceding asymptotic equivalence identifies the factorial expression with a fixed positive constant, $3/(4\pi^2)$, times the stated growth function. Multiplication by a nonzero constant preserves asymptotic order, and the growth function is of the same order as itself. Transitivity of asymptotic order therefore gives the result.

**Key facts.** `FABL.levelThreeFactorialConstant_isEquivalent`.
