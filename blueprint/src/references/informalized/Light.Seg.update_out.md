<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.update_out -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating outside a segment

**Claim.** If a function agrees with a list on the segment starting at $a$, then changing its value at an index strictly before the segment or at or beyond its end leaves the segment values unchanged.

**Proof.** By the segment agreement transfer principle (Light.Seg.congr), it suffices to show that the updated function agrees with the original at each position $a+i$ in the segment. The update location $b$ lies outside the segment: either $b<a$, so $b<a+i$, or $a+|l|\le b$, while $i<|l|$ gives $a+i<a+|l|\le b$. Thus $a+i\ne b$ in either case, and updating at $b$ leaves the value at $a+i$ unchanged.

**Key facts.** `Light.Seg.congr`.
