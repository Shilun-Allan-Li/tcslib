<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clHeaderLayout_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact recorder header layout

**Claim.** For the specified values $Q=C(|x|+1)^e$, $m=|x|+Q$, and $T=c(A(m+1)^d+1)^2$, the recorder layout formed from the arithmetic header encoding, an all-false word of length $m$, and a clock of $T$ true bits is exactly the prepared recorder words followed by the four fields $x$, the binary representation of $Q$, that of $m$, and that of $T$.

**Proof.** Unfold the layout and header encodings, and compare the two functions on tape indices. For indices in the recorder’s internal block, the five successive nested pairs are decoded to their second components; the pair-encoding decoding identity (`Turing.pairDecode_pairEncode`) shows that these recover the prepared false word and clock, while the recorder’s buffer field is the corresponding fourth field. For indices in the four header slots, the same identity, applied successively to the nested pairs, shows that the extracted fields are $x$, the bits of $Q$, the bits of $m$, and the bits of $T$, in order. Since the two layouts agree at every index, the functions are equal.

**Key facts.** `Turing.pairDecode_pairEncode`.
