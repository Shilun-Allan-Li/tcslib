<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.RandReducible.of_polyTimeReducible_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Composing Polynomial and Randomized Reductions

**Claim.** If $A$ is polynomial-time reducible to $B$ and $B$ is randomized-reducible to $C$, then $A$ is randomized-reducible to $C$.

**Proof.** Let $g$ be a polynomial-time many-one reduction from $A$ to $B$, and let the randomized reduction from $B$ to $C$ use a map $f$, parameters $a,k$, and its stated probability guarantee. For input $x$, feed that randomized reduction the encoding of $g(x)$ together with its random string; the reduction map is therefore $f$ applied to the corresponding slice of the encoded input. This map is polynomial-time: the output length of $g$ is polynomially bounded (`PolyTimeComputable.output_length_le`), the required random-string length is bounded by the resulting polynomial length estimate, and the maps for encoding, decoding, slicing, and composition preserve polynomial-time computability (`PolyTimeComputable.comp`, `PolyTimeComputable.pairEncode`, `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`, `polyTimeComputable_sliceTake`). The length estimate ensures that the random bits consumed by the slice are no more than the number available in the encoded input. The probability of success with this padded random string equals the original reduction's probability, by the padding identity for random-bit probabilities (`randProb_take`). Finally, the many-one reduction property gives $g(x)\in B$ exactly when $x\in A$, so the success event for the composed reduction is the required one; this event substitution preserves probability (`randProb_congr`). The original probability guarantee consequently yields the guarantee for the composed reduction.

**Key facts.** `Complexity.PolyTimeComputable.output_length_le`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Randomized.polyTimeComputable_sliceTake`, `Randomized.randProb_take`, `Randomized.randProb_congr`.

**Caveat.** The supplied upstream statements do not include the definitions of the reduction relations or the probability guarantee in the randomized-reduction witness. The proof source shows the encoding and probability-padding route, but the exact success-event specification cannot be fully spelled out from the supplied material.
