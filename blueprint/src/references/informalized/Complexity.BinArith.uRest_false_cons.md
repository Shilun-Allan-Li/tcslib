<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.uRest_false_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-rest output after false

**Claim.** For every finite bit string $w$, the unary-rest transducer maps an input beginning with false and followed by $w$ to $w$.

**Proof.** The initial false bit emits no output and moves the transducer to the true state. From that state, it copies every subsequent input bit unchanged; this is the fact that the transducer started in the true state reproduces its input (`transduce_rest_true`). Hence the output is exactly $w$.

**Key facts.** `Complexity.BinArith.transduce_rest_true`.
