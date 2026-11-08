<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.polyTimeComputable_codesW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Code Generation

**Claim.** For all natural numbers $B$ and $e$, the function mapping a bit string $x$ to its associated code word is polynomial-time computable.

**Proof.** The update `codeStep` is polynomial-time computable: it extracts the two components of its input, adds one to the first component, and pairs that result with the accumulated word and the old first component. These operations preserve polynomial-time computability (Complexity.BinArith.polyTimeComputable_add, Complexity.polyTimeComputable_pairFstD, Complexity.polyTimeComputable_pairSndD, Complexity.PolyTimeComputable.append, and Complexity.PolyTimeComputable.pairEncode). The code word is obtained by iterating this update $B(|x|+1)^e$ times from a fixed initial encoding, then decoding the second component. To apply the polynomial-iteration bound (Complexity.BinArith.polyTimeComputable_iterate), use the identity describing the iterate as an encoding of the iteration count and the encoded binary words below it (Randomized.BPLInP.iterate_codeStep). The encoded list has length at most $V(2V+2)$ for $V$ words (Randomized.BPLInP.length_encWords_range_le); each binary representation has length at most its represented number (Turing.length_bits_le_self), and pairing has length $2|u|+2+|v|$ (Turing.length_pairEncode). With $V=B(|x|+1)^e$, these estimates give a polynomial bound in $|x|$ for every intermediate iterate. The iteration result is therefore polynomial-time computable, and extracting its second component yields `codesW`.

**Key facts.** `Complexity.BinArith.polyTimeComputable_add`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.append`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_const`, `Randomized.BPLInP.iterate_codeStep`, `Randomized.BPLInP.length_encWords_range_le`, `Turing.length_bits_le_self`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_iterate`.
