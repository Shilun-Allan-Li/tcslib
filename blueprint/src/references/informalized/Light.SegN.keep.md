<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SegN.keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of a natural segment

**Claim.** If $\mu$ agrees with the natural-number list $l$, viewed as integers, on the segment from $a$, and $\mu'$ agrees with $\mu$ throughout that segment, then $\mu'$ agrees with the same list there.

**Proof.** Use the segment-preservation property (Light.Seg.keep) for the integer-valued list obtained by viewing each entry of $l$ as an integer. Its required agreement of the two functions at every segment position follows from the hypothesis that they agree throughout the segment. Unfolding the natural-number segment notation yields the claimed conclusion.

**Key facts.** `Light.Seg.keep`.
