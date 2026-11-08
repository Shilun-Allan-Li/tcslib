<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneCascadeRight_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cascade Leaves Higher Zones Unchanged

**Claim.** For any level $k$ above the $j$ levels of a rightward cascade, both its left and right words remain unchanged.

**Proof.** Induct on $j$, generalizing over the zone contents. When $j=0$, the cascade has no paired shifts; its possible level-zero move cannot affect level $k$, since $k>0$. For the successor step, decompose the cascade as a paired shift at level $j+1$, the length-$j$ cascade, and another paired shift at level $j+1$ (`zoneCascadeRight_succ`). Because $k>j+1$, it is neither of the two levels affected by either paired shift. The paired-shift frame property therefore leaves both words at level $k$ unchanged at each outer shift (`zoneStepPair_frame`). Also $k>j$, so the induction hypothesis applies to the middle cascade. Combining these equalities proves the result.

**Key facts.** `Turing.zoneCascadeRight_succ`, `Turing.zoneStepPair_frame`.
