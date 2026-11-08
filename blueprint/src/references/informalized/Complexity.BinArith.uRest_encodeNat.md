<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.uRest_encodeNat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-rest removes unary encoding

**Claim.** For every natural number $j$ and finite bit string $w$, the unary-rest transducer maps the unary encoding of $j$ followed by $w$ to $w$.

**Proof.** Induct on $j$. For $j=0$, the input is just the false delimiter followed by $w$. Reading that delimiter switches the transducer into the state that copies every remaining bit, so the output is $w$. In the successor step, the input has one extra true bit before the encoding considered in the induction hypothesis. While in its initial state, the transducer discards that true bit and remains in that state; it therefore reduces to the induction-hypothesis input, whose output is $w$.
