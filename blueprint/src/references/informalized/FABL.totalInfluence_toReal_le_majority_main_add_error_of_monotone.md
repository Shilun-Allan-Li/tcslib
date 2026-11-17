<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.totalInfluence_toReal_le_majority_main_add_error_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-dimensional majority influence bound

**Claim.** For an odd number of coordinates, every monotone Boolean function has total influence at most the leading square-root term for majority plus the defined majority error.

**Proof.** The majority influence identity (\texttt{totalInfluence\_majority\_odd\_eq\_main\_add\_error}) rewrites the stated right-hand side as the total influence of majority on $2m+1$ coordinates. Apply the monotone-function influence bound (\texttt{totalInfluence\_toReal\_le\_majority\_of\_monotone}) to $f$ and majority in that dimension. Substituting the identity gives the claimed inequality.

**Key facts.** `FABL.totalInfluence_majority_odd_eq_main_add_error`, `FABL.totalInfluence_toReal_le_majority_of_monotone`.
