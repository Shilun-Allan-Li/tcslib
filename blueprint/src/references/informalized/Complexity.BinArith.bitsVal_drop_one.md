<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.bitsVal_drop_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After Dropping the First Bit

**Claim.** For every finite Boolean list $w$, the value after dropping its first bit is the quotient of the value of $w$ by $2$.

**Proof.** The value-from-the-first-bit identity (`bitsVal_eq_headD`) writes the value of $w$ as the value of its first bit plus twice the value after dropping that bit. A Boolean bit has value either zero or one, so this first contribution is less than two. Dividing the displayed decomposition by two therefore gives exactly the value after dropping the first bit.

**Key facts.** `Complexity.BinArith.bitsVal_eq_headD`.
