<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.cellOf_mkCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from Window Cells

**Claim.** Under the stated slot, head uniqueness, and head existence conditions, the reconstructed configuration lies in the radius-$s$ window and its encoded cells at all indices below $2s+1$ equal the prescribed cell values.

**Proof.** Fix a work tape. By head existence, there is an index below $2s+1$ marked as its head. Choose the least such index. The reconstruction places that tape's head at the corresponding position, namely the index minus $s$. Since the index is in the window, this position has absolute value at most $s$. The reconstruction assigns blank symbols outside the window by definition, so the reconstructed configuration satisfies both parts of the window condition.

Now fix any index $j<2s+1$. The slot condition says that the head-and-summary slot is present there exactly when $j=0$. At index $0$, the reconstructed state and output summary are read from the prescribed slot; at all other indices the slot is absent. For each tape, the reconstructed tape contents at the position represented by $j$ are read directly from the corresponding cell value, since that position is inside the window.

It remains to check the head markers. At the chosen least marked index, the reconstructed head position makes the marker true. At any other index, if its marker were also true, head uniqueness would force it to equal the chosen index. Thus its marker is false, matching the reconstructed head position. These componentwise agreements give equality between the encoding of the reconstructed configuration and the prescribed cell at every index in the window.
