<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SegN.take_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending a segment prefix

**Claim.** If the current function agrees with the integer cast of the first $k$ entries of $l$ on the segment starting at $a$, then updating it at $a+k$ to the integer represented by the $k$th entry makes it agree with the first $k+1$ entries there.

**Proof.** Apply the segment extension lemma (`Light.SegN.snoc`) to the prefix `l.take k`, appending the natural number `l.getD k 0`. It gives agreement with the list `(l.take k) ++ [l.getD k 0]`, while updating the function at $a+|l.take k|$. Since $k<|l|$, the prefix has length $k$, and `List.take_succ_getD` identifies this appended list with `l.take (k+1)`. The same length equality makes the update location $a+k$, yielding the stated agreement.

**Key facts.** `Light.SegN.snoc`, `List.take_succ_getD`.
