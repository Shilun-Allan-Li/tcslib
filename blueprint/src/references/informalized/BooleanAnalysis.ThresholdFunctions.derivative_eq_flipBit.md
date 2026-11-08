<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.derivative_eq_flipBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative under a bit flip

**Claim.** The discrete derivative at $x$ equals $(f(x)-f(x^i))/2$ multiplied by the sign encoding of the bit $x_i$.

**Proof.** Split according to whether $x_i$ is false or true. The update identity (`update_eq_ite_flipBit`) says that setting coordinate $i$ to a prescribed bit gives either the original point, when that bit already matches, or the point with coordinate $i$ flipped. If $x_i$ is false, the derivative is $(f(x)-f(x^i))/2$ and the sign encoding is $1$. If $x_i$ is true, the derivative is $(f(x^i)-f(x))/2$ and the sign encoding is $-1$. In both cases this is the stated expression.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.update_eq_ite_flipBit`.
