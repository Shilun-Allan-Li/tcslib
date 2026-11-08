<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.ring_choose_even_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even binomial coefficient recurrence

**Claim.** For every real $s$ and natural number $k$, $\binom{s}{2(k+1)}=\binom{s}{2k}(s-2k)(s-(2k+1))/((2k+1)(2k+2))$.

**Proof.** Apply the generalized binomial coefficient recurrence at the consecutive indices $2k$ and $2k+1$. These give $\binom{s}{2k+1}=\binom{s}{2k}(s-2k)/(2k+1)$ and $\binom{s}{2k+2}=\binom{s}{2k+1}(s-(2k+1))/(2k+2)$. Substituting the first identity into the second and combining the denominators yields the stated recurrence, since $2(k+1)=2k+2$.
