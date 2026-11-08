<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_normalizedGotsmanLinialTotalInfluence_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even subsequence influence limit

**Claim.** For every fixed \(k>0\), the normalized total influence along dimensions \(k+2m\) tends to \(k\sqrt{2/\pi}\).

**Proof.** Factor the normalized total influence along this even subsequence as the product of \(\sqrt{k+2m}\) times the odd-majority influence and a finite sum of shifted binomial probabilities divided by that influence (\(\texttt{normalizedGotsmanLinialTotalInfluence\_even}\)). The first factor tends to \(\sqrt{2/\pi}\) (\(\texttt{tendsto\_sqrt\_shift\_mul\_oddMajorityInfluence}\)); the second tends to \(k\) (\(\texttt{tendsto\_sum\_shiftedBinomialProbability\_div\_oddMajorityInfluence}\)). The product limit is therefore \(k\sqrt{2/\pi}\).

**Key facts.** `FABL.normalizedGotsmanLinialTotalInfluence_even`, `FABL.tendsto_sqrt_shift_mul_oddMajorityInfluence`, `FABL.tendsto_sum_shiftedBinomialProbability_div_oddMajorityInfluence`.
