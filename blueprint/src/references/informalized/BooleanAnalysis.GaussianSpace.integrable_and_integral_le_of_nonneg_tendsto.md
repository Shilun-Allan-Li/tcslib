<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/FatouBound.lean :: BooleanAnalysis.GaussianSpace.integrable_and_integral_le_of_nonneg_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability and Bound for a Limit

**Claim.** If nonnegative integrable functions converge almost everywhere to an almost everywhere strongly measurable function and their integrals are bounded above by a convergent sequence, then the limit is integrable and its integral is at most the limit of those bounds.

**Proof.** For each approximating function, nonnegativity almost everywhere makes its integral equal to the integral of its norm. Fatou's lemma for the lower limit of the norms, together with almost-everywhere convergence, bounds the integral of the limit's norm by the lower limit of the approximating norm integrals. The assumed integral bounds and convergence of the bound sequence then show that this norm integral is finite and at most $c$. Almost-everywhere strong measurability and finite integral of the norm give integrability of $f$. Finally, $\int f\le |\int f|\le\int|f|\le c$, proving the claimed integral bound as well.
