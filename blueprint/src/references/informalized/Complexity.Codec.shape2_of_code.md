<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean :: Complexity.Codec.shape2_of_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape of a two-payload code

**Claim.** If the word has the stated nested pairing form and the configuration code at scale $s$ equals $c$, then it has the asserted two-payload shape, including the binary-length bound for $s$.

**Proof.** The pairing-form component of the shape is exactly the given equality. For the length bound, the code’s binary representation equals the configuration word (`bits_cfgCode`). After substituting the assumed code equality and the given nested pairing form, the configuration word is no longer than the full paired word. The general width bound for a configuration code then implies that the binary representation of $s$ is no longer than the binary representation of the full word’s length (`width_of_code`). The needed comparison of lengths follows from the length formula for pairing (`length_pairEncode`).

**Key facts.** `Complexity.Codec.bits_cfgCode`, `Complexity.Codec.width_of_code`, `Turing.length_pairEncode`.
