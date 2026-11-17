<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/JuntaStableInfluence.lean :: FABL.totalStableInfluence_eq_sum_of_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable influence on relevant coordinates

**Claim.** If a function depends only on the coordinates in $J$, its total stable influence equals the sum of its stable influences over coordinates in $J$.

**Proof.** For every coordinate outside $J$, dependence only on $J$ forces its stable influence to vanish (\texttt{stableInfluence\_eq\_zero\_of\_not\_mem\_of\_dependsOn}). Thus the sum over all coordinates is unchanged if each outside coordinate is replaced by zero. The resulting sum has nonzero terms only for coordinates in $J$, and is precisely the sum of stable influences over $J$.

**Key facts.** `FABL.stableInfluence_eq_zero_of_not_mem_of_dependsOn`.
