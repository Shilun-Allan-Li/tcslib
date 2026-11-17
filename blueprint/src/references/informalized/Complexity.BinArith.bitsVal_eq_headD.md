<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.bitsVal_eq_headD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value from the First Bit

**Claim.** For a finite Boolean word $w$, its value is the value of its first bit, taken as false when the word is empty, plus twice the value of the word after dropping its first bit.

**Proof.** Split into the empty-list case and the case where $w$ has first bit $b$ followed by a remaining list. In the empty case, both the list value and the value after dropping the first bit are zero, and the default first bit is false. In the nonempty case, the recursive definition of the value gives $b$'s value plus twice the value of the remaining list; dropping the first bit produces exactly that remaining list.
