<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.cfgWord_eq_bits_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Code and Bit Representation

**Claim.** The numerical code of the encoded configuration word equals $c$ if and only if that word is the binary bit list of $c$.

**Proof.** The code is the numerical value of the configuration word's bit list. The value-to-bits identity (`bits_cfgCode`) rewrites the bit list of that code as the configuration word itself. Therefore, if the code equals $c$, substituting this equality gives that the word is `Nat.bits c`. Conversely, if the word is `Nat.bits c`, then injectivity of the bit-list representation (`bits_injective`) shows that the code equals $c$.

**Key facts.** `Complexity.Codec.bits_cfgCode`, `Complexity.LogProg.bits_injective`.
