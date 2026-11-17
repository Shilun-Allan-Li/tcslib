<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.hasFalse_encodeNat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False Bit in a Natural Encoding

**Claim.** For every natural number $j$ and bit string $w$, the concatenation of the encoding of $j$ with $w$ contains a false bit.

**Proof.** Induct on $j$. When $j=0$, its encoding is the singleton false bit, so the concatenation contains a false bit. For the successor case, the encoding begins with a true bit followed by the encoding for $j$; the induction hypothesis supplies a false bit in that remaining encoding followed by $w$. Hence the successor encoding followed by $w$ also contains a false bit.
