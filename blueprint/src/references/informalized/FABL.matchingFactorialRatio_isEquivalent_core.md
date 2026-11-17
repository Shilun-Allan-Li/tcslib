<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.matchingFactorialRatio_isEquivalent_core -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial ratio asymptotic equivalent

**Claim.** For fixed $r>0$, as $k$ tends to infinity, the factorial ratio is asymptotic to the matching Stirling core: the quotient of the two tends to $1$.

**Proof.** The map $k\mapsto rk$ tends to infinity because $r$ is positive. Apply the factorial Stirling asymptotic equivalence along this map to obtain $(rk)!\sim \operatorname{Stirling}(rk)$. Also, raising the Stirling equivalence for $k!$ to the fixed power $r$ and multiplying both sides by the same factor $r^{rk}$ gives $(k!)^r r^{rk}\sim \operatorname{Stirling}(k)^r r^{rk}$. Taking the quotient of these two equivalences shows that the factorial ratio is asymptotic to the quotient of the Stirling approximations. For every $k\ge1$, the exact identity expressing that quotient as the matching Stirling core identifies the resulting comparison and proves the claim.

**Key facts.** `FABL.factorial_isEquivalent_factorialStirlingApprox`, `FABL.factorialStirlingApprox_matching_ratio_eq_core`.
