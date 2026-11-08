<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.factorial_bound_strong_lt_printed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Factorial Bound

**Claim.** If $r>0$ and $1<rk$, then multiplying $(rk)!<(rk!)^2$ by $((2r-1)/r)^{rk}$ preserves the strict inequality.

**Proof.** The hypothesis $r>0$ implies $2r-1>0$, so $((2r-1)/r)^{rk}$ is positive. Also, $1<rk$ implies $(rk)!>1$. For any real $x>1$, one has $x<x^2$; apply this to $x=(rk)!$. Multiplication by the positive factor therefore gives the required strict inequality.
