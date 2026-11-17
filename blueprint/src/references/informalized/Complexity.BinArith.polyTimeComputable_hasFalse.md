<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_hasFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time False-Bit Detection

**Claim.** The function that returns a one-bit word indicating whether a finite Boolean word contains a false bit is polynomial-time computable.

**Proof.** First transform each bit by Boolean negation. A one-state transducer that emits the negation of each input bit is polynomial-time computable (`polyTimeComputable_transduce`), and induction over the word shows its output is exactly the pointwise negation of the input. Applying the polynomial-time ‘any true bit’ test to this transformed word detects precisely whether the original word contains a false bit. Polynomial-time computability is preserved by composition (`PolyTimeComputable.comp`), so the resulting one-bit output is polynomial-time computable (`polyTimeComputable_any`).

**Key facts.** `Complexity.polyTimeComputable_transduce`, `Complexity.BinArith.polyTimeComputable_any`, `Complexity.PolyTimeComputable.comp`.
