<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.pairEncode_nil_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending to an empty encoded component

**Claim.** Appending $b$ to the encoding of $(a,\varnothing)$ gives the encoding of $(a,b)$.

**Proof.** The encoding consists of the doubled-bit encoding of $a$, followed by the delimiter $[0,1]$ and then its second component. When that component is empty, appending $b$ places it immediately after the delimiter. This is precisely the encoding of $(a,b)$.
