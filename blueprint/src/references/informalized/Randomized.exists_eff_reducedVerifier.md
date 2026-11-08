<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.exists_eff_reducedVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficient Reduced Verifier

**Claim.** Composing an efficient verifier with a polynomial-time computable map f, while restricting its random string to the prescribed prefix length based on |f(x)|, preserves efficiency; that required length is itself bounded by a polynomial in |x|.

**Proof.** Let C,c bound the output length of f, so |f(x)|≤C(|x|+1)^c (`Complexity.PolyTimeComputable.output_length_le`). Construct a map g that decodes a pair (x,r), applies f to x, takes the prefix of r of length polyLen(a,k,|f(x)|), and encodes the resulting pair. The pairing decoders, the map f, and the prefix-taking map are polynomial-time computable; closure under composition and pairing therefore makes g polynomial-time computable (`Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Randomized.polyTimeComputable_sliceTake`). On an encoded pair, g produces exactly the encoding of f(x) and the required prefix, by the definition of the slice operation.

Take the preimages under g of the two polynomial-time languages witnessing efficiency of the original verifier. Preimages of P languages under polynomial-time maps remain in P (`Complexity.preimage_mem_P`). The pair-decoding identity then shows that these languages witness efficiency of the reduced verifier.

For the length bound, put p=|x|+1, which is at least one. The output bound gives |f(x)|+1≤C p^c+p^c=(C+1)p^c. Raising to k and multiplying by a preserves the inequality. Finally, a((C+1)p^c)^k equals a(C+1)^k p^{ck), so choose a'=a(C+1)^k and k'=ck.

**Key facts.** `Complexity.PolyTimeComputable.output_length_le`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Randomized.polyTimeComputable_sliceTake`, `Complexity.preimage_mem_P`.
