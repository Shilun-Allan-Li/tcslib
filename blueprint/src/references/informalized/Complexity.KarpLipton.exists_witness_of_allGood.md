<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.exists_witness_of_allGood -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A witness follows from good specifications

**Claim.** If no triple violates the good-specification conditions, then for each length-$m$ string $u$ there is a length-$m$ string $v$ such that $(\langle x,u\rangle,v)\in V$, where $m=C(|x|+1)^c$.

**Proof.** Set $m=C(|x|+1)^c$. The root query, with a marker of $m$ ones followed by $0$, must be accepted: otherwise the empty choices of $j,p$ would satisfy the first bad case. We now descend through the binary-prefix tree. For each $i\le m$, construct a string $p$ of length $i$ such that the query with marker length $m-i$ and suffix $0p$ accepts. At $i=0$, this is the root query. Suppose it holds at $i<m$, and take such a prefix $p$ of length $i$. If both children, obtained by extending $p$ by $0$ and by $1$, were rejected, then the accepted parent query can be written with marker length $m-i-1$ and suffix $1 0 p$. The equality $(m-i-1)+|p|+1=m$ holds, so this would be the third bad case, contradicting the assumption. Hence at least one child query accepts, giving a prefix of length $i+1$ with the required property. Iterating to $i=m$ gives an accepted query for a full-length prefix $p$. If $(\langle x,u\rangle,p)\notin V$, this accepted leaf query would satisfy the second bad case. Therefore it belongs to $V$, and its length is $m$.
