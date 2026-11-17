<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration on the $L^1$-Concentrating Family

**Claim.** For positive $\epsilon$, the Fourier spectrum of $f$ is $\epsilon$-concentrated outside the family consisting of those sets whose coefficient magnitude, multiplied by the Fourier one-norm, is at least $\epsilon$.

**Proof.** Write $L$ for the Fourier one-norm and let $\mathcal F$ be the specified family. The one-norm is nonnegative. If $L=0$, the sum of the nonnegative absolute Fourier coefficients is zero, so every coefficient is zero; consequently the weight outside $\mathcal F$ is zero.

Now suppose $L>0$. If $S$ is outside $\mathcal F$, the membership criterion for this family implies $L|\widehat f(S)|<\epsilon$. Multiplying this inequality by the nonnegative coefficient magnitude and dividing by $L$ gives $\widehat f(S)^2\le (\epsilon/L)|\widehat f(S)|$. Sum over the sets outside $\mathcal F$, then enlarge the sum to all coordinate sets; the summands are nonnegative. The resulting sum is $(\epsilon/L)L=\epsilon$, by the definition of the one-norm. This proves the concentration bound.

**Key facts.** `FABL.fourierOneNorm_nonneg`, `FABL.mem_l1ConcentratingFourierFamily`.
