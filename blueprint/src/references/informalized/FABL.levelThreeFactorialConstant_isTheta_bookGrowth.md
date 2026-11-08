<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.levelThreeFactorialConstant_isTheta_bookGrowth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial constant and book growth

**Claim.** As $d$ tends to infinity through the natural numbers, $\frac{(3d)!^2}{(d!)^6}$ is of the same asymptotic order as $\frac{9^{3d}}{(3d)^2}$; their ratio is eventually bounded above and below by positive constants.

**Proof.** The growth function is exactly nine times the book growth function at every $d$. Thus it has the same asymptotic order as the book growth function, since scaling by the nonzero constant nine preserves that order. Combining this comparison with the previously established fact that the factorial expression has the order of the growth function, transitivity yields the claimed comparison.

**Key facts.** `FABL.levelThreeFactorialConstant_isTheta`, `FABL.levelThreeGrowth_eq_nine_mul_bookGrowth`.
