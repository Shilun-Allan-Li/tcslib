<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRowPrefix_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for a Stored Row Prefix

**Claim.** If each coordinate word has length at most $W$, then for every $j$ the stored row prefix of length $j$ has length at most $j(2W+2)$.

**Proof.** Induct on $j$. The empty prefix has length zero. For the successor step, the definition appends either the encoding of coordinate $j$ or, if that coordinate is out of range, the empty word. In the in-range case, that coordinate has length at most $W$, and its encoding has length $2|w_j|+2$: each bit contributes two copies and the encoding adds a two-bit separator. The induction hypothesis bounds the preceding prefix by $j(2W+2)$, so adding at most $2W+2$ gives $(j+1)(2W+2)$. In the out-of-range case nothing is appended, and the same successor bound follows directly from the induction hypothesis.
