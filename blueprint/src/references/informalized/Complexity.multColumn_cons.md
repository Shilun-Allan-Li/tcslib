<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multColumn_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Column for a Cons List

**Claim.** For a bit $t$, bit strings $a,b$, and $j\in\mathbb{N}$, the multiplication-column sum for $t::a$ is $t$ times the $j$th bit of $b$, plus zero if $j=0$ and otherwise the column sum for $a,b$ at $j-1$. Missing list entries count as zero.

**Proof.** Expand the column sum over the indices below the length of $t::a$. Its first summand, at index $0$, is included because $0\le j$ and contributes $t$ times the $j$th bit of $b$. The remaining indices have the form $p+1$ and range over the indices of $a$. If $j=0$, none of these satisfy $p+1\le j$, so their contribution is zero. If $j=k+1$, the condition becomes $p\le k$, and the second bit index becomes $(k+1)-(p+1)=k-p$; hence the remaining sum is exactly the column sum for $a,b$ at $k$.
