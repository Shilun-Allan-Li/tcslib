<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneShiftInW_capacity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capacity Under an Inward Shift

**Claim.** If every word has length at most the capacity of its zone, then after an inward shift at any level, every word still has length at most the capacity of its zone.

**Proof.** Fix a zone and inspect the cases in the definition of the inward shift. If the shift is inactive, the word is unchanged and its capacity bound is the hypothesis. If it is active, the donor zone is empty. At the lower of the two affected indices, the new word is a prefix of the upper word, of length at most $2^{i-1}$, which is the capacity of the lower zone. At the upper index, the new word is the suffix after removing $2^{i-1}$ entries from the old upper word; its length is no greater than the old length, so it remains within the upper zone's capacity. Every other index is unchanged and retains its assumed bound.
