<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.take_drop_flatMap_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extracting a concatenated block

**Claim.** If every list $f(z)$ for $z<m+n+c$ has length $k$, then dropping the first $mk$ entries from the concatenation of the lists indexed below $m+n+c$ and taking the next $nk$ entries gives the concatenation indexed by $m,m+n$ (that is, $m\le z<m+n$).

**Proof.** Split the index range into consecutive blocks of lengths $m$, $n$, and $c$. Their concatenated lists therefore appear in that order. The first block has total length $mk$, by the fact that a flatMap over an initial range of $r$ indices has length $rk$ when each constituent list has length $k$ (`List.length_flatMap_range`). Thus dropping $mk$ entries removes exactly the first block. The middle block has length $nk$ by the same fact, so taking the next $nk$ entries returns exactly that block.

**Key facts.** `List.length_flatMap_range`.
