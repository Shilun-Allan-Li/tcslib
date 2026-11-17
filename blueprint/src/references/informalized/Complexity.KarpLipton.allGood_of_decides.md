<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.allGood_of_decides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Good circuit decisions exclude bad specifications

**Claim.** Under the stated circuit-family and language hypotheses, no triple of strings can satisfy the length conditions and any of the three bad-specification cases.

**Proof.** Set $m=C(|x|+1)^c$. First establish a translation principle for each well-formed query: if its marker has length $k$ and its remaining suffix is $q$, with $k+|q|=m$, then the circuit query is equivalent to the existence of a completion $s$ such that $|q s|=m$ and the encoded pair $(\langle x,u\rangle,q s)$ belongs to $V$. Indeed, `length_query` identifies the query's total length with the prescribed circuit input length; `query_iff_mem_language` turns acceptance by the circuit into membership in its language; the equality of that language with the prefix language and `mem_prefixLang_iff` give the completion description. The identity `wLen_pairEncode` sets the required suffix length to $m$.

Now suppose a bad specification held. If its first case held, the root query would reject. But the hypothesis on $x$ and $u$ supplies a length-$m$ witness in $V$, so the translation principle says that this root query accepts, a contradiction.

If the second case held, the accepted leaf query would give a completion $s$ with $|p s|=m$. Since already $|p|=m$, the completion has length zero and hence is empty. Thus $(\langle x,u\rangle,p)\in V$, contradicting the asserted nonmembership.

Finally, suppose the third case held. The accepted parent query has suffix $1 0 p$, preceded by $|j|$ marker ones. Rewriting this as a marker of length $|j|+1$ followed by $0p$, the translation principle gives a completion $s$ with $|p s|=m$. The length equation $|j|+|p|+1=m$ forces $s$ to be a single bit followed by a string $s'$. Let that bit be $b$. The same completion shows that the child query with marker length $|j|$ and suffix $p b$ accepts. If $b=0$, this contradicts the first child rejection; if $b=1$, it contradicts the second. All three possibilities are impossible.

**Key facts.** `Complexity.KarpLipton.length_query`, `Complexity.KarpLipton.query_iff_mem_language`, `Complexity.KarpLipton.mem_prefixLang_iff`, `Complexity.KarpLipton.wLen_pairEncode`.
