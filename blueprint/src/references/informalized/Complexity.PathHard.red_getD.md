<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.red_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bits of the Reduction String

**Claim.** The reduction string has the stated unary prefix, separator, adjacency block, and five-bit tail, with out-of-range positions interpreted as false.

**Proof.** Write $n$ for the vertex count. The reduction is nested pair encoding, so apply the pair-encoding bit formula first to its outer unary prefix. Positions below $2n$ read the doubled unary word and are true; the next two positions are the separator bits, false then true (`pairEncode_getD`). Beyond them, apply the same formula to the inner pair. Within the adjacency block, the offset is less than $2n^2$; halving it identifies the corresponding adjacency-word index. The adjacency word has length $n^2$, and its lookup is the edge indicator at the quotient and remainder by $n$ (`length_adjWordE`, `adjWordE_getD`). Past this block, subtract its length and read the remaining offset in the encoded pair of binary endpoint words. Those endpoints are $0$ and $1$, so the residual suffix is exactly $[0,1,0,1,1]$, with the default value false beyond it. The displayed cases distinguish these regions, and the natural-number arithmetic identifies their offsets.

**Key facts.** `Complexity.pairEncode_getD`, `Complexity.PathHard.length_adjWordE`, `Complexity.PathHard.adjWordE_getD`.
