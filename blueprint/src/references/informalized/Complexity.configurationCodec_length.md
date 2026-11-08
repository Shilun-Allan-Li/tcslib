<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationCodec_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Code Length

**Claim.** For any parameters and any configuration, the configuration code has length exactly $C(s+n+1)$.

**Proof.** If the input has length $n$, the code is a padded code word, whose length is its specified length by `codecWord_length`. If the input length differs from $n$, the code is a list of false bits repeated exactly that many times. In either case its length is $C(s+n+1)$.

**Key facts.** `Complexity.codecWord_length`.
