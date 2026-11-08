<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SameOutside2.update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation under an interior update

**Claim.** If two sequences agree outside both intervals and the update index lies in at least one interval, updating the second sequence there preserves their agreement outside both intervals.

**Proof.** Agreement outside both intervals means agreement on the set of indices satisfying both outside conditions. If the update index $c$ lies in either interval, it fails the corresponding outside condition, so it is not in this set. The update therefore leaves every value on the set unchanged, and the original agreement continues to hold. This is the preservation of agreement under updating outside its domain (Light.SameOn.write).

**Key facts.** `Light.SameOn.write`.
