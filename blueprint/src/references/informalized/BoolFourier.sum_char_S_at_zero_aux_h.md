<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.sum_char_S_at_zero_aux_h -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character at the Origin

**Claim.** The function sending each subset of coordinates to the value of its Walsh character at the all-zero vector is constantly $1$.

**Proof.** For each subset $S$, the character at the all-zero vector equals $1$ by `char_S_of_zero`. Since the two functions agree at every subset, they are equal.

**Key facts.** `BoolFourier.char_S_of_zero`.
