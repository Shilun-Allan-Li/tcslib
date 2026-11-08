<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.csKey_gives -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Key expression evaluates safely

**Claim.** For every item index $i<n$ and integers $c,p$, the key-loading expression is safe in the indicated loop state and evaluates to $kf(i)$, provided the counting-sort preconditions and the stated memory-agreement condition hold.

**Proof.** First, source-memory agreement gives that the source cell for item $i$ contains $it(i)$ in the modified memory (CountSort.Pre.item). The key cell for that item lies outside both the destination and counter intervals, so the memory-agreement hypothesis implies that it still contains its original key value, namely $kf(i)$. The expression computes the item’s source address, loads the item, forms its designated key address, and loads that cell. The address arithmetic therefore yields the designated key cell, and the final load returns $kf(i)$. For safety, the bounds on the source and key cells ensure that each load address is valid; the space-to-word bound ensures these addresses fit within the word limit (Limits.Addr.abs_le). The key-cell bound and the same word bound also make the address arithmetic safe. Thus the expression is safe and has the asserted value.

**Key facts.** `Light.CountSort.Pre.item`, `Light.Limits.Addr.abs_le`.
