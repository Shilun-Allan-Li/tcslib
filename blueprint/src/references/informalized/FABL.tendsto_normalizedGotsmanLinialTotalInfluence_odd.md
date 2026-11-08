<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_normalizedGotsmanLinialTotalInfluence_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd subsequence influence limit

**Claim.** For every fixed \(k>0\), the normalized total influence along dimensions \(k+2m+1\) tends to \(k\sqrt{2/\pi}\).

**Proof.** Along this subsequence, factor the normalized total influence into \(\sqrt{k+2m+1}\) times the odd-majority influence and a finite sum of shifted binomial probabilities divided by that influence (\(\texttt{normalizedGotsmanLinialTotalInfluence\_odd}\)). The first factor tends to \(\sqrt{2/\pi}\), using the square-root shift limit with shift \(k+1\) (\(\texttt{tendsto\_sqrt\_shift\_mul\_oddMajorityInfluence}\)). The finite-sum factor tends to \(k\) (\(\texttt{tendsto\_sum\_shiftedBinomialProbability\_div\_oddMajorityInfluence}\)). Multiplying these limits gives the claimed value.

**Key facts.** `FABL.normalizedGotsmanLinialTotalInfluence_odd`, `FABL.tendsto_sqrt_shift_mul_oddMajorityInfluence`, `FABL.tendsto_sum_shiftedBinomialProbability_div_oddMajorityInfluence`.
