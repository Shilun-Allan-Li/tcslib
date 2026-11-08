<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.query_suffix_value_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Suffix Value Bound

**Claim.** For every finite Boolean word $w$ and every $j\in\mathbb{N}$, the value of the suffix obtained by deleting the first $j$ bits is at most the value of $w$.

**Proof.** Induct on $j$, with the word generalized so the argument applies to any remaining suffix. When $j=0$, the suffix is the whole word. For the successor step, the empty word gives the claim immediately. If $w=b::v$, deleting the first $j+1$ bits gives the same suffix as deleting the first $j$ bits from $v$. By induction its value is at most the value of $v$. The value of $b::v$ is $b.toNat+2\,\mathrm{bitsVal}(v)$, which is at least $\mathrm{bitsVal}(v)$; hence it also bounds the value of the desired suffix.
