<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.sq_integral_le_integral_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of the integral bound

**Claim.** For a finite probability space and a real-valued function $f$, the square of its integral is at most the integral of its square.

**Proof.** Apply the finite-measure-space inequality that, for a probability measure $\mu$ and a real-valued function $f$, $(\int f\,d\mu)^2\leq\int f^2\,d\mu$ (\texttt{FiniteMeasureSpace.sq_integral_le_integral_sq}). The finite probability space supplies the required finite-measure structure and probability measure through its volume measure, giving the desired inequality.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.sq_integral_le_integral_sq`.

**Caveat.** The supplied informal statement describes a broader Jensen and norm-monotonicity result, but the formal statement and proof establish only the displayed square-integral inequality.
