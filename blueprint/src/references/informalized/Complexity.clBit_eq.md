<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBit_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Digits Are Determined by Their Values

**Claim.** For Boolean digits, equality of their numeric values, with true represented by one and false by zero, is equivalent to equality of the digits.

**Proof.** Check the four possible pairs. If both digits are false or both are true, their numeric values agree and the digits agree. If exactly one is true, their values are zero and one, so neither equality holds. This proves both directions.
