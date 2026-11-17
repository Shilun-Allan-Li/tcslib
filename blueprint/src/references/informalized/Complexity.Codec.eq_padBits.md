<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.eq_padBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List equals its padded binary representation

**Claim.** A Boolean list $p$ equals the least-significant-first binary expansion of its value, followed by false entries until the result has length $|p|$.

**Proof.** The binary-expansion-with-padding identity says that $p$ is the binary expansion of its value followed by exactly $|p|-|\mathrm{bits}(\mathrm{bitsVal}(p))|$ false entries. By the definition of $\mathrm{padBits}$, that expression is $\mathrm{padBits}(|p|,\mathrm{bitsVal}(p))$, as required.

**Key facts.** `Complexity.Codec.eq_bits_append_replicate`.
