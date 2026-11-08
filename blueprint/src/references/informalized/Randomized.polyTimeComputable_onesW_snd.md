<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.polyTimeComputable_onesW_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Second-Component Filtering

**Claim.** Decoding the second component of a bit string, using the empty string if decoding fails, and deleting every zero from it is polynomial-time computable.

**Proof.** The aligned-pair decoder's second-component function is polynomial-time computable. The transducer that scans a word and outputs a $1$ exactly when its current input bit is $1$ is also polynomial-time computable, by the general result for finite-state transducers. Composing this transducer with the second-component decoder gives the required function.

**Key facts.** `Complexity.polyTimeComputable_transduce`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_app`.
