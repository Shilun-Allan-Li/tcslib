<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.polyTimeComputable_isZero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Zero Test

**Claim.** The function returning $[\mathsf{true}]$ exactly when the value of a Boolean word is zero is polynomial-time computable.

**Proof.** The binary value of a word is zero exactly when the word has no true entry (`bitsVal_eq_zero_iff`). Thus the desired output is the negation of the one-bit result of the test for whether any entry is true. That test is polynomial-time computable (`polyTimeComputable_any`), and polynomial-time Boolean negation preserves this property (`polyTimeComputable_not`). The two Boolean outputs agree in both cases of the any-test, yielding the desired function.

**Key facts.** `Complexity.BinArith.bitsVal_eq_zero_iff`, `Complexity.BinArith.polyTimeComputable_any`, `Complexity.polyTimeComputable_not`.
