<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneCascadeRight_blocked -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blocked Cascade Preserves Contents

**Claim.** If each left word below level $j$ and the left word at level $j$ are full, then the rightward cascade through $j$ levels preserves the concatenated left-side and right-side words.

**Proof.** Proceed by induction on the number $j$ of levels, allowing the zone contents to vary in the induction hypothesis. For $j=0$, fullness of the level-zero left word prevents the initial rightward move, so the cascade leaves the contents unchanged. For the successor case, fullness at level $j+1$ prevents the shift-out condition at that level: the required additional capacity is positive, but the zone is already full. Thus the first paired shift leaves the entire left family unchanged. In particular, the hypotheses that the lower left zones are full remain true for the first $j$ levels. Apply the induction hypothesis to the contents after this paired shift; it preserves both concatenated sides through the inner cascade. The successor decomposition expresses the full cascade as this inner cascade bracketed by paired shifts at level $j+1$ (`zoneCascadeRight_succ`). Each paired shift preserves the concatenation of each side (`zoneStepPair_side`), so the two outer shifts do not change either concatenated word.

**Key facts.** `Turing.zoneCascadeRight_succ`, `Turing.zoneStepPair_side`.
