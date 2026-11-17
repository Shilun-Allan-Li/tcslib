<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.bits_cfgCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Configuration Encoding

**Claim.** For a configuration $C$ on input $x$ and space parameter $s$, the binary expansion of its numerical code is exactly the Boolean word encoding that configuration with parameter $s$.

**Proof.** The configuration word is canonical (`canon_cfgWord`). The canonical-word characterization says that any canonical Boolean word equals the binary expansion of its own binary value (`canon_eq_bits`). Since the configuration code is defined as the value of that word, applying the characterization and reversing the equality gives the claimed identity.

**Key facts.** `Complexity.Codec.canon_cfgWord`, `Complexity.LogProg.canon_eq_bits`.
