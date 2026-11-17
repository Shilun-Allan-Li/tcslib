<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluence_sq_mul_wallis -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Wallis identity for squared influence

**Claim.** For every $m\ge0$, the squared odd-majority influence satisfies $I_m^2(2m+1)W_m=1$.

**Proof.** Write the Wallis factor using its factorial ratio. By the definition of $I_m$ and the factorial formula for the central binomial coefficient, the left side becomes the product of the squared ratio $\bigl(m!/(2^ {2m}\,m!)\text{ with the central-binomial numerator included}\bigr)$ and the Wallis factorial ratio. More explicitly, substituting $\binom{2m}{m}=(2m)!/(m!)^2$ into $I_m=\binom{2m}{m}/2^{2m}$ and substituting the factorial expression for $W_m$ leaves cancelling factorial and power-of-two factors, with product exactly $1$.
