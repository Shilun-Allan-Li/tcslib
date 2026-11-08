<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.randProb_xor_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under a Fixed Bitwise Mask

**Claim.** For a uniformly random bit string $r$ of length $m$, the probability that a property $P$ holds of the bitwise XOR of $c$ and $r$ equals the probability that $P$ holds of $r$.

**Proof.** Represent the random string by a vector $r$ indexed by the $m$ positions. Map it to the vector whose entries are $c_i\mathbin{\mathrm{xor}}r_i$. This map is its own inverse, since applying the same mask twice cancels it at every coordinate. It therefore bijects the vectors satisfying the masked property with those satisfying $P$ itself, so the two finite sets have equal cardinality. Translating vectors to their corresponding lists uses the coordinatewise description of `zipWith` on lists built from finite vectors (`zipWith_ofFn`). Both probabilities have the same denominator $2^m$, so equality of the counts proves the result.

**Key facts.** `Randomized.zipWith_ofFn`.
