<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrAcceptanceProbability_le_exerciseSevenTwentyNine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OXR Acceptance Upper Bound

**Claim.** If $0\le\delta\le1/2$, then for odd bounded $f$ and any degree cutoff $t$, its OXR acceptance probability is at most $\frac34+\frac\delta4+\frac14\sqrt{(1-\delta)^t}+\frac14\sum_{|S|\le t}\widehat f(S)^2B_\delta(S)$, where $B_\delta(S)$ is the random-subset average of the absolute Fourier coefficient.

**Proof.** First express the acceptance probability using the OXR acceptance identity. The odd-function noise-stability bound gives $-\operatorname{Stab}_{-\delta}(f)\le\delta$. The Fourier-sum estimate bounds the negative of the remaining weighted Fourier sum by the square-root tail term plus the low-degree sum with absolute Fourier averages. Applying these two estimates to the identity and collecting terms yields the stated upper bound.

**Key facts.** `FABL.oxrAcceptanceProbability_eq_equationSevenSeven`, `FABL.neg_noiseStability_neg_le_of_odd`, `FABL.neg_oxrFourierSum_le_low_add_tail`.
