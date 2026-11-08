<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/CodePrefix.lean :: Complexity.TimeHierarchy.scanPre_pairEncode_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested Pair Encoding

**Claim.** Appending the paired encoding of $\alpha$ and $w$ to the prefix retained by scanning that encoding yields the encoding of $\alpha$ paired with the encoding of $\alpha$ and $w$.

**Proof.** By the paired-encoding scan identity (`scanPre_pairEncode`), scanning the encoding retains precisely the doubled bits of $\alpha$ followed by the delimiter. Appending the original encoding then appends that same delimiter and $w$. By the definition of pair encoding, the resulting list is the encoding of $\alpha$ with the entire encoding of $\alpha$ and $w$ as its suffix.

**Key facts.** `Complexity.TimeHierarchy.scanPre_pairEncode`.
