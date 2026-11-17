<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.blocksEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Block under the Bijection

**Claim.** For natural numbers $n,b$, a bit string $r$ indexed by the $nb$ positions, and an index $i$ among the first $n$ positions, the integer represented by the $i$th block under the standard bijection between length-$b$ bit strings and integers from $0$ to $2^b-1$ equals the value of the length-at-most-$b$ substring beginning at position $ib$.

**Proof.** First identify the substring after dropping $ib$ bits and taking $b$ bits with the length-$b$ list whose $j$th bit is the original bit at position corresponding to $(i,j)$ under the standard splitting of the $nb$ positions into $n$ blocks of size $b$. The index bound $i<n$ ensures these positions lie in range; equality of the lists follows by checking their entries. The block bijection applies the bit-string-to-integer bijection to exactly this length-$b$ function. Its value is the list value by `Randomized.bitsEquiv_apply`, proving the claimed equality.

**Key facts.** `Randomized.bitsEquiv_apply`.
