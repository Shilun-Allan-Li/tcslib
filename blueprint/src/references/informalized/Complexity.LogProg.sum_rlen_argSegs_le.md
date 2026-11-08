<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.sum_rlen_argSegs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Argument Segment Length Bound

**Claim.** If every word in $ws$ has length at most $W$, then the sum of the lengths of its argument segments, counting doubled segments twice and the final segment once, is at most $|ws|(2W)$.

**Proof.** Every segment produced from `ws` comes from one of its words: if a segment belongs to `argSegs ws`, its underlying word belongs to `ws` (`Complexity.LogProg.mem_argSegs`). Thus that word has length at most $W$. If the segment is doubled, its length is twice the word length and is at most $2W$; if it is not doubled, its length is at most $W$, hence also at most $2W$. There are at most $|ws|$ segments, so summing this uniform bound gives at most $|ws|(2W).

**Key facts.** `Complexity.LogProg.mem_argSegs`.
