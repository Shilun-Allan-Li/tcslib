<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BerryEsseenIntervals.lean :: FABL.measureReal_Iio_eq_leftLim_cdf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Limit of the Cumulative Distribution Function

**Claim.** For a probability measure $\nu$ on $\mathbb{R}$, the measure of $(-\infty,x)$ equals the left limit at $x$ of its cumulative distribution function.

**Proof.** First, the cumulative distribution function is nonnegative, and its monotonicity implies that its left limit at $x$ is nonnegative: compare its value at $x-1$ with that left limit. The measure associated to the cumulative distribution function agrees with $\nu$; the Stieltjes-measure formula for the interval $(-\infty,x)$ identifies its measure with the real value of the left limit minus the value at $-\infty$. Since that endpoint value is zero, this is the real value of the left limit. Nonnegativity lets us convert that value from extended reals without change.
