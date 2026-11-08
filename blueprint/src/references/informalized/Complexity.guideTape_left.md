<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.guideTape_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Location of the left edge marker

**Claim.** For every radius $R$ and integer coordinate $z$, the guide tape carries the left edge marker at $z$ exactly when $z=-R-1$.

**Proof.** Unfold the definition of the guide tape. If $z=-R-1$, the first branch assigns the left edge marker. Conversely, for any other $z$, that first condition fails. The later branches assign the right edge marker, origin, inside mark, or no symbol, none of which is the left edge marker. Thus the marker occurs exactly at the stated coordinate.
