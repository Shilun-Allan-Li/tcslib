<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.totalInfluence_evenMajority_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Even Majority Influence

**Claim.** If $f$ is a majority function on the $(2m+2)$-dimensional cube, its total influence is $(2m+1)\binom{2m}{m}/2^{2m}$.

**Proof.** Replace the total influence of $f$ by that of majority in dimension $2m+1$, using the even-to-odd equality (`FABL.totalInfluence_evenMajority_eq_oddMajority`). The exact odd-majority formula (`FABL.totalInfluence_majority_odd`) evaluates this as $(2m+1)\binom{2m}{m}/2^{2m}$, as claimed.

**Key facts.** `FABL.totalInfluence_evenMajority_eq_oddMajority`, `FABL.totalInfluence_majority_odd`.
