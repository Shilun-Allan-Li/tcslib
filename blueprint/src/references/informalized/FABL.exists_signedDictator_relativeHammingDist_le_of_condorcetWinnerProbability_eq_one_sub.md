<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.exists_signedDictator_relativeHammingDist_le_of_condorcetWinnerProbability_eq_one_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closeness to a signed dictator

**Claim.** If the three-candidate Condorcet winner probability is $1-\epsilon$ and $(9/2)\epsilon\leq1/1600$, then the Boolean function is within relative Hamming distance $1601(9/2)\epsilon$ of some signed dictator.

**Proof.** Set $\delta=(9/2)\epsilon$, which is nonnegative and at most $1/1600$. The Condorcet probability bound says that the probability is at most $7/9+(2/9)W^1[f]$ (`FABL.condorcetWinnerProbability_le`). Substituting the assumed probability $1-\epsilon$ and rearranging yields $1-\delta\leq W^1[f]$. The FKN theorem, with this $\delta$, then supplies a coordinate and a choice of sign whose dictator is at relative Hamming distance at most $1601\delta$ (`FABL.fkn`). Substituting the definition of $\delta$ gives the stated bound.

**Key facts.** `FABL.condorcetWinnerProbability_le`, `FABL.fkn`.
