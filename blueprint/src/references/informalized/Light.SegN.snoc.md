<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SegN.snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a value to a segment

**Claim.** If $\mu$ agrees with $l$, viewed as integers, on the segment starting at $a$, then updating its value at $a+|l|$ to the integer represented by $x$ makes it agree with the list obtained by appending $x$ to $l$.

**Proof.** Apply the segment-appending property (Light.Seg.snoc) to the integer-valued list corresponding to $l$, appending the integer represented by $x$. This gives agreement with the appended integer list after updating at the endpoint $a+|l|$. That integer list is exactly the image of $l++[x]$ under the natural-to-integer map, so the result is the asserted natural-number segment agreement.

**Key facts.** `Light.Seg.snoc`.
