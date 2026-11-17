<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SegN.of_sameOutside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation outside a disjoint segment

**Claim.** If $\mu$ agrees with the natural-number list $l$ on the segment starting at $b$, and $\mu'$ agrees with $\mu$ outside the segment from $a$ of length $n$, then the same values of $l$ are preserved whenever the two segments are disjoint.

**Proof.** Apply the outside-preservation property for segments (Light.Seg.of_sameOutside) to the integer list obtained by viewing each entry of $l$ as an integer. The hypothesis $b+|l|\le a$ or $a+n\le b$ says the segment starting at $b$ lies wholly before or wholly after the segment from $a$ of length $n$. The assumed agreement of $\mu'$ and $\mu$ outside that latter segment therefore preserves every value on the former segment. Interpreting the integer list as the image of $l$ gives the stated natural-number segment conclusion.

**Key facts.** `Light.Seg.of_sameOutside`.
