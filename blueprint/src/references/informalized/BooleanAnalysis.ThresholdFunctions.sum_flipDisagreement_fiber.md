<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.sum_flipDisagreement_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summed fiber disagreement identity

**Claim.** For a Boolean function taking values in $\{-1,1\}$, summing its flip-disagreement over all coordinate colorings equals $m^n$ times its noise sensitivity at parameter $1/m$.

**Proof.** Because the function takes only the values $\pm1$, its disagreement under a flip can be expressed through its Fourier coefficients as one half of one minus the sum over sets $T$ of $(-1)^{|T\cap S|}\widehat f(T)^2$, where $S$ is the flipped set (`flipDisagreement_eq`). Apply this with $S$ equal to the fiber of each coloring. Summing over colorings, interchange the finite sums over colorings and $T$. For each fixed $T$, the parity sum over colorings is $m^n(1-2/m)^{|T|}$ (`sum_pi_sign`). Thus the sum of the disagreement terms becomes $m^n$ times one half of the difference between the total Fourier weight and the Fourier sum weighted by $(1-2/m)^{|T|}$. The stability formula identifies that weighted sum with noise stability at correlation $1-2/m$ (`stability_formula`). Since this correlation equals $1-2(1/m)$, the resulting expression is precisely $m^n$ times the noise sensitivity at parameter $1/m$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.flipDisagreement_eq`, `BooleanAnalysis.ThresholdFunctions.sum_pi_sign`, `BooleanAnalysis.stability_formula`.
