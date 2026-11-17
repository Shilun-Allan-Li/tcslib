<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.identifiedNegation_flip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping an identified variable

**Claim.** Flipping coordinate $j_0$ of $w$ changes exactly those coordinates of the XOR input whose indices lie in the fiber of $j_0$ under $\pi$.

**Proof.** First express the negated identification at the flipped input using the XOR formula from `identifiedNegation_apply`. It remains to compare the resulting Boolean input with the original XOR input after flipping the fiber. Fix $i$. If $\pi(i)=j_0$, then $i$ belongs to that fiber, and flipping $w$ at $j_0$ negates $w_{\pi(i)}$; after XOR with $z_i$, this is exactly the flip of the original XOR coordinate. If $z_i$ is false this is immediate, while if it is true the two Boolean negations cancel in the required way. If $\pi(i)\ne j_0$, then $i$ is outside the fiber and the value of $w$ at $\pi(i)$ is unchanged by the flip, so the XOR coordinate is unchanged as well. The inputs agree at every coordinate, proving the identity.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.identifiedNegation_apply`, `BooleanAnalysis.ThresholdFunctions.mem_fiber`.
