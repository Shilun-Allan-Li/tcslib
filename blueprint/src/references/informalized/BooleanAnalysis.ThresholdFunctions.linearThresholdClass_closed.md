<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.linearThresholdClass_closed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under negation and identification

**Claim.** Negating selected inputs and identifying coordinates of a $\{-1,1\}$-valued linear threshold function produces another $\{-1,1\}$-valued linear threshold function.

**Proof.** Take an affine representation $f(x)=\operatorname{thresholdSign}(c+\sum_i a_i\,\operatorname{boolToSign}(x_i))$ of the given linear threshold function; such a representation exists by `IsLinearThreshold.exists_affine`. After the prescribed input negations, each signed input satisfies
\[\operatorname{boolToSign}(z_i\mathbin{\mathrm{xor}}w_{\pi(i)})=\operatorname{boolToSign}(z_i)\operatorname{boolToSign}(w_{\pi(i)}),\]
where the left side denotes the Boolean value selected by the definition of identified negation. Thus the coefficient of the signed variable at coordinate $j$ is the sum of $a_i\operatorname{boolToSign}(z_i)$ over all $i$ with $\pi(i)=j$. Regrouping the original finite sum by the fibers of $\pi$ shows that the transformed function is the threshold of the affine form with constant term $c$ and these grouped coefficients. Every such affine threshold is linear threshold (`isLinearThreshold_affine`), and threshold signs always take values in $\{1,-1\}$ (`isPmOne_thresholdSign`). Together these establish membership in the linear threshold class.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.IsLinearThreshold.exists_affine`, `BooleanAnalysis.ThresholdFunctions.isLinearThreshold_affine`, `BooleanAnalysis.ThresholdFunctions.isPmOne_thresholdSign`.
