<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.LevelKParityTuple.chosenCompatibleMatching_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility of the chosen matching

**Claim.** The matching selected by the existence theorem is compatible with the assigned vertex labeling: the endpoints of every matching edge have the same label.

**Proof.** The existence theorem supplies a perfect matching whose edges join vertices with equal assigned labels. The chosen matching is defined to be the matching component of that existential witness. Its accompanying witness therefore states exactly that its edges have equal endpoint labels.

**Key facts.** `FABL.LevelKParityTuple.exists_compatible_matching`.
