<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLargestFourierCoefficient.lean :: FABL.tendsto_oddMajorityInfluence_div_main -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-majority influence asymptotic

**Claim.** The odd-majority influence divided by its stated main term tends to one.

**Proof.** The odd arity \(2m+1\) tends to infinity, so its reciprocal tends to zero. Hence \(1+1/(2m+1)\) tends to one. The main term is positive, and the two influence bounds give, after division by it, \(1\leq \operatorname{Inf}/\operatorname{Inf}_{\rm main}\leq 1+1/(2m+1)\): the lower bound is \(\texttt{oddMajorityInfluenceMain\_le}\), and the upper bound follows from \(\texttt{oddMajorityInfluence\_le\_main\_add}\). The squeeze theorem proves the limit.

**Key facts.** `FABL.oddMajorityInfluenceMain_le`, `FABL.oddMajorityInfluence_le_main_add`.
