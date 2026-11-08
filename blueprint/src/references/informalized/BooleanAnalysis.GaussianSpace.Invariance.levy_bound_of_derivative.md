<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.levy_bound_of_derivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimized Lévy distance bound

**Claim.** The derivative-based integral error hypothesis implies that the Lévy distance is at most $((m+2)+2^m)B^{1/(m+2)}$.

**Proof.** First apply the scale bound (`levy_bound_at_scale`): for every $\eta>0$, the Lévy distance is at most $(m+2)\eta+(2^m/\eta^{m+1})B$. The optimization lemma (`levy_bound_of_scale`) converts this family of bounds, together with $B\ge0$, into the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.levy_bound_at_scale`, `BooleanAnalysis.GaussianSpace.Invariance.levy_bound_of_scale`.
