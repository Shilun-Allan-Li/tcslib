<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.sameFrame_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of empty frames

**Claim.** The zero-padded frames of two empty lists are equal.

**Proof.** At every natural-number index, both frames return the default value $0$, since neither list has an entry there. Thus the two frame functions agree pointwise and are equal.
