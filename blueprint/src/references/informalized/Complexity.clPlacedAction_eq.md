<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPlacedAction_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula for a placed action

**Claim.** A placed action preserves the input-head movement, output symbol, and mapped successor state; on each host tape it uses the selected source tape's action when that tape is occupied, and otherwise leaves the tape unchanged.

**Proof.** Unfolding the placed action and the embedded action shows that its host-tape action at index $j$ is determined by the source index found by searching the placement's image. The placement lookup identity (`Complexity.clPlacement_lookup`) identifies that search result with the selector: it is the selected source index when $j$ is occupied, and no source index otherwise. Substituting this identity gives the stated host-tape action. The other components follow directly from the definitions: input movement and output are preserved, while the successor state is mapped by the given state map.

**Key facts.** `Complexity.clPlacement_lookup`.
