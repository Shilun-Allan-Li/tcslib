<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.bitsVal_mod_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value Modulo Two

**Claim.** For every finite Boolean word, the remainder of its value upon division by $2$ is the value of its first bit, taken as false when the word is empty.

**Proof.** The value-from-the-first-bit identity (`bitsVal_eq_headD`) expresses the word's value as its first bit's value plus twice another natural number. The first bit's value is zero or one, hence already lies in the range of remainders modulo two. The doubled term contributes no remainder, proving the claim, including the empty word through the default false bit.

**Key facts.** `Complexity.BinArith.bitsVal_eq_headD`.
