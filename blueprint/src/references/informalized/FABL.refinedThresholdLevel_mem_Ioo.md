<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.refinedThresholdLevel_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of the Refined Threshold Level

**Claim.** For every $\tau\in(0,1)$, the refined threshold level $\tau/(1+\tau)$ lies strictly between $0$ and $1/2$.

**Proof.** Since $\tau>0$, both the numerator $\tau$ and denominator $1+\tau$ are positive, so their quotient is positive. For the upper bound, the positive denominator allows the inequality $\tau/(1+\tau)<1/2$ to be checked by cross-multiplication; it reduces to $2\tau<1+\tau$, which follows from $\tau<1$.
