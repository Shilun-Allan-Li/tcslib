<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.polyTimeComputable_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Binary Addition

**Claim.** The function on bit strings that decodes the two components of a pair, interprets each component as a natural number with the first bit least significant, adds those numbers, and returns the binary expansion of their sum is polynomial-time computable.

**Proof.** First compute the serial output of the carry-and-sum-bit procedure on the two decoded components, padded to a common length, and then normalize that output by replacing it with the canonical binary expansion of its value. Polynomial-time computability is preserved under composition, so the serial procedure followed by normalization is polynomial-time (`Complexity.PolyTimeComputable.comp`, together with `Complexity.BinArith.polyTimeComputable_serial` and `Complexity.BinArith.polyTimeComputable_normBits`). It remains to check that this composite has the claimed value. Set $N=|z|+2$, where $z$ is the input, and let $a,b$ be its decoded components. Their lengths are at most $|z|$, so each value is less than $2^{|z|}$; consequently $a+b<2^N$. The serial addition identity says that the value of its output plus $2^N$ times the final carry is $a+b$ (with initial carry false). Since $a+b<2^N$, the final carry must be zero, and the serial output therefore has value $a+b$. Normalization turns it into the binary expansion of that sum, as required.

**Key facts.** `Complexity.BinArith.polyTimeComputable_serial`, `Complexity.BinArith.polyTimeComputable_normBits`, `Complexity.PolyTimeComputable.comp`, `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`, `Complexity.BinArith.serial_add`, `Complexity.LogProg.bitsVal_lt_two_pow`.
