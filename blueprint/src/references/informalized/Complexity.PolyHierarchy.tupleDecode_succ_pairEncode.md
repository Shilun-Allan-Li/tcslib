<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.tupleDecode_succ_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tuple decoding of an encoded pair

**Claim.** At level $n+1$, decoding an encoded pair $(w,v)$ with parameter $s$ produces the encoding of the level-$n$ decoding of $w$ paired with $\mathrm{dec}(s,v)$.

**Proof.** At a successor level, tuple decoding is defined by pairing the preceding-level decoding of the first decoded component with the decoder applied to the second decoded component. The pair encoding law says that decoding the encoding of $(w,v)$ returns exactly $(w,v)$. Substituting these components into the recursive definition gives the claimed identity.
