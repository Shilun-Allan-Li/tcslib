<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.tendsto_inverseDimensionHalfNoiseParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Dimension Parameter Limit

**Claim.** The sequence of inverse dimension parameters tends to zero through positive values in the half interval.

**Proof.** First, the real sequence $n\mapsto 1/n$ tends to $0$ as $n\to\infty$. For every $n\ge 2$, the inverse dimension parameter equals $1/n$, so it agrees with this sequence eventually; changing finitely many initial terms does not affect the limit. The subtype convergence criterion then gives convergence to $0$ in the half interval. To obtain convergence through positive values, observe that the parameter is positive for every $n$: in the case $n\ge2$ it is $1/n$, and otherwise it is $1/2$. Thus the sequence is eventually in the positive part of the interval, as required for the neighborhood restricted to positive parameters.
