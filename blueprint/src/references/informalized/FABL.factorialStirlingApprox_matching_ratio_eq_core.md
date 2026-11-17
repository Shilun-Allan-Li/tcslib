<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.factorialStirlingApprox_matching_ratio_eq_core -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Approximation Ratio Identity

**Claim.** For positive integers $r$ and $k$, the ratio $A(rk)/(A(k)^r r^{rk})$ equals $C(r,k)$.

**Proof.** Set $x=k/e$. Since $(rk)/e=r(k/e)$, the power in the numerator is $(rx)^{rk}=r^{rk}x^{rk}$. The power from the denominator is $((k/e)^k)^r=x^{rk}$, by the rule for powers of powers. These factors cancel against the explicit $r^{rk}$ in the denominator. The remaining square-root factors give $\sqrt{2rk\pi}/(\sqrt{2k\pi})^r$, which is exactly $C(r,k)$.
