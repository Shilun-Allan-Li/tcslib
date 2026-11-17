<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.length_encodeList_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for List Encoding Length

**Claim.** If every element encoding $f(a)$ for $a$ in $as$ has length at most $B$, then the encoding of $as$ has length at most $|as|(B+1)+1$.

**Proof.** Induct on $as$. The empty list encodes as one terminator bit, giving the bound with list length zero. For a list with head $a$ and tail $as'$, the hypothesis bounds the head encoding length by $B$, and the induction hypothesis applies to the tail because every tail entry also belongs to the original list. The encoding adds one separator bit, the head encoding, and the tail encoding. These lengths are at most $1+B+|as'|(B+1)+1$, which equals $|a::as'|(B+1)+1$.
