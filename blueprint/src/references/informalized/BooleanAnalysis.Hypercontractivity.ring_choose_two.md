<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.ring_choose_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second generalized binomial coefficient

**Claim.** For every real number $s$, the generalized binomial coefficient of order two is $\binom{s}{2}=s(s-1)/2$.

**Proof.** The identity relating consecutive generalized binomial coefficients gives $2\,\binom{s}{2}=s\,\binom{s-1}{1}$. Since the generalized binomial coefficient of order one is its upper argument, this becomes $2\,\binom{s}{2}=s(s-1)$. Dividing by $2$ yields the formula.
