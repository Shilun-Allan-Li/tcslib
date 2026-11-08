<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.granularityFrequencyWithin_eq_univ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Criterion for the full frequency set

**Claim.** The frequencies in $J$ that also lie in $U$ comprise all of $J$ exactly when $J\subseteq U$.

**Proof.** Suppose the frequency set is all of $J$. For any $i\in J$, regard $i$ as an element of the subtype $J$. It belongs to the filtered frequency set, hence its underlying index lies in $U$. This proves $J\subseteq U$. Conversely, if $J\subseteq U$, every element of the subtype $J$ passes the filter, so the filtered set equals the whole subtype.

**Key facts.** `FABL.mem_granularityFrequencyWithin`.
