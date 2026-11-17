<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.length_padBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Padded Bit String

**Claim.** If the binary expansion of $v$ has length at most $w$, padding it with zeros to length $w$ gives a bit string of length exactly $w$.

**Proof.** The padded string is the concatenation of the bit string of $v$ and a list of $w-(\operatorname{length}(\mathrm{bits}(v)))$ zeros. Its length is therefore $\operatorname{length}(\mathrm{bits}(v)) + w-\operatorname{length}(\mathrm{bits}(v))=w$, using the assumed length bound to interpret the subtraction in the natural numbers.
