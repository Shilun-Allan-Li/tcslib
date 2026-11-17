<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_column_prefix_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading-bit column recurrence

**Claim.** For a leading bit $t$ and finite bit strings $a,b$, the weighted sum of the first $n+1$ multiplication columns of $t::a$ equals $t$ times the value of the first $n+1$ bits of $b$, plus twice the corresponding first $n$ weighted columns of $a$.

**Proof.** First replace the prefix value of $b$ by its weighted-bit sum, using the identity that the sum of the first $m$ weighted bits is the value of the length-$m$ prefix (`mult_bits_prefix`). Expand each column of $t::a$ into the contribution from its leading bit and the shifted column of $a` (`multColumn_cons`). Splitting off the last term in each range sum leaves the leading-bit contributions for indices $0$ through $n$ and the shifted contributions for indices $1$ through $n$. Reindexing those shifted terms gives twice the sum of the first $n$ columns of $a$; the remaining factors are rearranged by ordinary distributivity. The result follows by collecting these two parts.

**Key facts.** `Complexity.mult_bits_prefix`, `Complexity.multColumn_cons`.
