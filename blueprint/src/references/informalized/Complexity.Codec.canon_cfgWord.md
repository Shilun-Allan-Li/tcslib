<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.canon_cfgWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Configuration Encoding

**Claim.** The Boolean string encoding any configuration in a window of radius $s$ is nonempty and has final bit true.

**Proof.** The encoding is a concatenation ending in the one-element list $[\mathrm{true}]$. Consequently it is nonempty and its final bit is true. This is exactly the defining condition for the encoding to be canonical.
