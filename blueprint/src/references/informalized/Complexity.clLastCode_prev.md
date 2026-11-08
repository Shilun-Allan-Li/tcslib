<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLastCode_prev -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Previous Visit Code

**Claim.** The code of the index immediately before the last true entry in the work-tape head-position flag word equals the code of the greatest earlier time when the head was at its position at time $t$, with the code empty when there is no such time.

**Proof.** Apply the marker-scan identity (`Complexity.clLastIndex_marker`) to the flag predicate that records whether the head position at time $s$ equals its position at time $t$. It identifies the length of the prefix before the last true flag with the last index where that predicate holds. Then apply the last-index-as-filtered-maximum identity (`Complexity.clLastIndex_max`): this index is the maximum of the filtered range of times below $t$. The resulting filtered list is exactly the one used to define `prevVisit`; the Boolean equality test in that definition agrees with the stated equality predicate. Applying the optional-time code to these equal optional indices gives the claimed equality, including the empty case.

**Key facts.** `Complexity.clLastIndex_marker`, `Complexity.clLastIndex_max`.
