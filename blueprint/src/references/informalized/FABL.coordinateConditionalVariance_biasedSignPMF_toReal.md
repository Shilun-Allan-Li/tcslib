<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.coordinateConditionalVariance_biasedSignPMF_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance Under Biased Sign Resampling

**Claim.** For a Boolean function and a coordinate resampled from the biased sign law, the conditional variance is $4p(1-p)$ when flipping that coordinate changes the function value, and is zero otherwise.

**Proof.** Let $x_+$ and $x_-$ be the inputs obtained from $x$ by setting coordinate $i$ to $1$ and $-1$, respectively. The resampled coordinate has probabilities $1-p$ and $p$ at these two values (\texttt{pmfExpectation\_biasedSignPMF}). Since the function takes only the two signs, its values at $x_+$ and $x_-$ either coincide or are opposite. If they coincide, the resampled function is constant and its variance is zero. If they are opposite, its mean is $(1-p)f(x_+)+pf(x_-)$; the deviations from this mean have magnitudes $2p$ and $2(1-p)$, respectively. The variance is consequently $(1-p)(2p)^2+p(2(1-p))^2=4p(1-p)$. The current input $x$ is one of $x_+$ and $x_-$, and flipping coordinate $i$ gives the other, so the two values differ exactly when $f(x)\ne f(\mathrm{flipCoordinate}(x,i))$. Finally, $\mathrm{biasSigma}(p)^2=4p(1-p)$ by \texttt{biasSigma\_sq}, giving the claimed indicator formula. The proof checks the two possible current signs and the two possible values of $f$ at $x_+,x_-$.

**Key facts.** `FABL.pmfExpectation_biasedSignPMF`, `FABL.setCoordinate_eq_self`, `FABL.biasSigma_sq`.
