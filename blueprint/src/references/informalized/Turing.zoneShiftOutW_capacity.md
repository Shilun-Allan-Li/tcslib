<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneShiftOutW_capacity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capacity Under an Outward Shift

**Claim.** If every word has length at most the capacity of its zone, then after an outward shift at any level, every word still has length at most the capacity of its zone.

**Proof.** Fix a zone and split according to whether the outward shift is active. If it is inactive, the word is unchanged and the assumed capacity bound applies. When active, the lower zone receives a prefix of its original word, so its length is at most the lower zone's capacity. The upper zone receives the remaining suffix of the lower word followed by the old upper word. Because the lower word is full, removing its first $2^{i-1}$ entries leaves exactly the amount needed to fill the lower zone's capacity; the activation condition bounds the length of this remainder together with the old upper word by the upper zone's capacity. All other zones are unchanged.
