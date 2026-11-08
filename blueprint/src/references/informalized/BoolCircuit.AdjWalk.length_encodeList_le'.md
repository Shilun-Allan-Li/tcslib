<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjWalk.length_encodeList_le' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Length Bound for Lists

**Claim.** If every element of a finite list $as$ is assigned a bit string of length at most $b$, then the encoding of $as$ has length at most $|as|(b+1)+1$.

**Proof.** Proceed by induction on the list. For the empty list, its encoding is the one-bit list `[false]`, so the bound holds with equality. For a list $a::as$, the hypothesis bounds the length of $f(a)$ by $b$, and the induction hypothesis applies to the tail because each of its elements also belongs to $a::as$. The encoding begins with one marker bit, followed by $f(a)$ and then the encoding of the tail. Its length is therefore at most $1+b+(|as|(b+1)+1)=(|as|+1)(b+1)+1$, which is the required bound.
