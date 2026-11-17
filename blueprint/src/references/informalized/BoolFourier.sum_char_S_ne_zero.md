<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.sum_char_S_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character Sum Away from the Origin

**Claim.** If a Boolean vector is not the all-zero vector, then the sum of its Walsh character values over all coordinate subsets is zero.

**Proof.** Because $x$ is not the all-zero vector, some coordinate $i$ has value true. The pairing identity `sum_char_S_ne_zero_aux_h_pair` shows that the sum over all subsets equals the sum of the negatives of those same character values, by pairing subsets according to whether they contain this coordinate. The latter sum is the negative of the original sum. Hence the sum equals its own negative, and therefore is zero.

**Key facts.** `BoolFourier.sum_char_S_ne_zero_aux_h_pair`.
