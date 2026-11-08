<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SameOutside.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity outside an interval

**Claim.** An integer-valued sequence agrees with itself at every index outside any given interval.

**Proof.** Agreement on any specified set is reflexive: at each index in that set, the sequence's value equals itself. Applying this to the indices outside the interval proves the claim.

**Key facts.** `Light.SameOn.refl`.
