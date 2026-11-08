<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.totalInfluence_evenMajority_eq_odd_main_add_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Majority Main Term and Error

**Claim.** For a majority function on the $(2m+2)$-dimensional cube, its total influence is the stated main term for dimension $2m+1$ plus the odd-majority error.

**Proof.** Replace the total influence of the given even-dimensional majority function by that of majority in dimension $2m+1$, using the even-to-odd majority influence equality (`FABL.totalInfluence_evenMajority_eq_oddMajority`). Then apply the decomposition of odd-majority influence into its main term and error (`FABL.totalInfluence_majority_odd_eq_main_add_error`).

**Key facts.** `FABL.totalInfluence_evenMajority_eq_oddMajority`, `FABL.totalInfluence_majority_odd_eq_main_add_error`.
