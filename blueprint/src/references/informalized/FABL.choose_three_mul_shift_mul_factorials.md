<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.choose_three_mul_shift_mul_factorials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial Coefficient Factorial Identity

**Claim.** For natural numbers $m,d$, $\binom{m+6d}{3d}(3d)!(m+3d)!=(m+6d)!$.

**Proof.** Apply the standard factorial formula for a binomial coefficient: if $r\le N$, then $\binom Nr r!(N-r)!=N!$. Take $N=m+6d$ and $r=3d$, for which $3d\le m+6d$. Since $(m+6d)-3d=m+3d$, the formula gives exactly the asserted identity.
