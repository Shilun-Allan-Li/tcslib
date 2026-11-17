<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.polyTimeComputable_hcCD3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Threefold Coin Construction

**Claim.** The function applying the unary multiplication construction to the pair of retained $1$ bits and the unary multiplication output built from the fourfold iteration result paired with $111$ is polynomial-time computable.

**Proof.** First, pair the fourfold length-limited iteration output from the decoded first component with the constant word $111$. Pair encoding and constant-output functions are polynomial-time computable. Applying unary multiplication to this pair remains polynomial-time computable by closure under composition. Next, pair that result with the string retaining the $1$ bits of the decoded second component; this is polynomial-time computable by closure under pair encoding. A final application of unary multiplication, again by composition, gives exactly the threefold coin construction.

**Key facts.** `Randomized.polyTimeComputable_hlDWord`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_mulU`, `Complexity.BinArith.polyTimeComputable_app`, `Randomized.polyTimeComputable_onesW_snd`.
