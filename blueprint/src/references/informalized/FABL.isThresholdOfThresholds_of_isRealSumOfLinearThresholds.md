<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.isThresholdOfThresholds_of_isRealSumOfLinearThresholds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold of linear thresholds

**Claim.** If a Boolean function is a real constant plus a sum of $s$ linear threshold functions, it is itself a threshold of those same functions.

**Proof.** Write the given representation as $f(x)=c+\sum_{i=1}^s g_i(x)$, interpreting the signs as real numbers. Use the same functions $g_i$ as the inner linear thresholds, assign weight $1$ to each, and use offset $c$. Their weighted sum is exactly the real value of $f(x)$. Since that value is either $1$ or $-1$, applying the threshold sign with zero assigned sign $+1$ returns $f(x)$ in either case. The assumed linear-threshold property of each $g_i$ is retained.
