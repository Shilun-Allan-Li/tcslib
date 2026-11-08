<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.searchInv_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Search Invariant

**Claim.** For every input bit string, the initial search state satisfies the stated search invariant with $c=2^{\lceil\log_2(2|z|)\rceil}+1$, $d=2$, and the bit false.

**Proof.** Choose $c=2^{\operatorname{clog}_2(2|z|)}+1$, $d=2$, and the bit false. The doubling-loop specification says its first component is a string of $\operatorname{clog}_2(2|z|)$ zeros followed by one; its represented value is therefore $2^{\operatorname{clog}_2(2|z|)}$. The following increment in the initialization makes the first encoded value exactly $c$, while the second and third components are the binary representation of $2$ and the false bit. By the least-prime bound, $c$ is strictly below the chosen least prime above the threshold and hence is at most that prime; it is also strictly above the threshold. We have $2\le d\le c$, since every power of two is at least one. There is no integer $m$ with $2\le m<2$, so the divisor exclusion is vacuous, and the condition on the bit is immediate because the bit is false.

**Key facts.** `Complexity.BinArith.dblLoop_spec`, `Complexity.BinArith.bitsVal_replicate_false_one`, `Complexity.BinArith.two_pow_lt_lovaszPrime`.
