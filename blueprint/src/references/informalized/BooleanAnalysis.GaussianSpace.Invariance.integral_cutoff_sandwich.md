<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.integral_cutoff_sandwich -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral Bounds for a Cutoff

**Claim.** A continuous function taking values in $[0,1]$, equal to $1$ on $(-\infty,u]$ and to $0$ on $[v,\infty)$, has integral between the measures of $(-\infty,u]$ and $(-\infty,v]$, expressed as real numbers.

**Proof.** The range bound makes $\phi$ integrable for the finite measure $\mu$. For the lower bound, compare $\phi$ pointwise with the indicator of $(-\infty,u]$: on that set both equal $1$, and off it the indicator is zero while $\phi\ge 0$. Integrating gives the lower inequality, since the integral of that indicator is the measure of the set. For the upper bound, compare $\phi$ with the indicator of $(-\infty,v]$: on the set $\phi\le 1$, while outside it the cutoff condition gives $\phi=0$. Integrating gives the upper inequality. The indicator integrals are the corresponding measures, viewed as real numbers.
