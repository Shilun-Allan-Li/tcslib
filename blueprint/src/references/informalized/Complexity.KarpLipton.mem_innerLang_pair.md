<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.mem_innerLang_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Membership in the Inner Language

**Claim.** The encoding of $x$ paired with $U$ belongs to the inner language exactly when no triple of bit strings $u,j,p$ satisfies the bad specification for $x$ and $U$.

**Proof.** Suppose first that the encoded pair lies in the inner language. To test an arbitrary triple $u,j,p$, use the outer test string that encodes the pair $(u,j)$ and then pairs it with $p$. The total projections recover $x$ and $U$ from the resulting nested encoding (the projection identities `gx_pair` and `gU_pair`). By the membership characterization of the bad language (`mem_badLang`), the bad specification for this test string is precisely the one for $x,U,u,j,p$. Inner-language membership excludes that test string from the bad language, so the specification cannot hold. Conversely, suppose no triple satisfies the specification. For any test string $t$, membership of the encoding of $(x,U)$ paired with $t$ in the bad language, by `mem_badLang`, gives a bad specification whose first two arguments reduce to $x$ and $U$ by `gx_pair` and `gU_pair`; its remaining arguments are the total projections of $t$. This contradicts the assumed absence of every such triple. Thus every test string is outside the bad language, as required.

**Key facts.** `Complexity.KarpLipton.gx_pair`, `Complexity.KarpLipton.gU_pair`, `Complexity.KarpLipton.mem_badLang`.
