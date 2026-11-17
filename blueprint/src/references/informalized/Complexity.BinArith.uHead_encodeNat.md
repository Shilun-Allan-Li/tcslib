<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.uHead_encodeNat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary encoding output

**Claim.** For every natural number $j$ and finite Boolean word $w$, the unary-head transducer maps the concatenation of $j$ true bits, a false bit, and $w$ to exactly $j$ true bits.

**Proof.** Induct on $j$. When $j=0$, the input begins with the false delimiter, which produces no output and leaves the transducer in a state that produces no further output; hence the result is empty. For the successor step, the input has one additional true bit at the front. That bit emits one true bit and leaves the transducer in its original true state, so the remaining input is handled as in the induction hypothesis. Thus the output consists of $j+1$ true bits.
