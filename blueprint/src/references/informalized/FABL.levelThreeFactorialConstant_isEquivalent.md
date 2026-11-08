<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.levelThreeFactorialConstant_isEquivalent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial constant asymptotic

**Claim.** As $d$ tends to infinity through the natural numbers, $\frac{(3d)!^2}{(d!)^6}$ is asymptotic to $\frac{3}{4\pi^2}\,\frac{3^{6d}}{d^2}$, meaning that the ratio tends to $1$.

**Proof.** First, the map $d\mapsto 3d$ tends to infinity with $d$. Composing the factorial Stirling asymptotic with this map shows that $(3d)!$ is asymptotic to its Stirling approximation at $3d$. The same Stirling asymptotic at $d$, raised to the sixth power, approximates $(d!)^6$. Taking the quotient of these asymptotic equivalences, and squaring the numerator equivalence, reduces the claim to the exact identity for the Stirling approximations: for every positive $d$, their quotient is $\frac{3}{4\pi^2}\,\frac{3^{6d}}{d^2}$. Since all sufficiently large natural numbers are positive, this identity identifies the eventual comparison function and proves the asserted asymptotic equivalence.

**Key facts.** `FABL.factorial_isEquivalent_factorialStirlingApprox`, `FABL.factorialStirlingApprox_three_ratio_eq`.
