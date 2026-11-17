<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.uHead_false_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-head output after false

**Claim.** For every finite bit string $w$, the unary-head transducer outputs the empty string on an input beginning with false.

**Proof.** The initial false bit emits nothing and sends the transducer to the false state. From that state, the transducer emits nothing on every subsequent bit; this is the fact that the transducer started in the false state produces empty output (`transduce_head_false`). Therefore the whole output is empty.

**Key facts.** `Complexity.BinArith.transduce_head_false`.
