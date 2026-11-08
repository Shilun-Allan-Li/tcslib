<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.shape_of_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape of a configuration code

**Claim.** If the word has the stated pairing form and the configuration code at scale $s$ equals $c$, then it has the asserted shape, including the binary-length bound for $s$.

**Proof.** The pairing-form component is the assumed equality. For the length component, the binary representation of the configuration code is the configuration word (`bits_cfgCode`). Substituting the code equality and pairing form reduces the needed comparison to the fact that the configuration word is no longer than a paired word containing it (`cfgWord_le_length`). Applying the width bound for configuration codes gives that the binary representation of $s$ is no longer than the binary representation of the full word’s length (`width_of_code`).

**Key facts.** `Complexity.Codec.bits_cfgCode`, `Complexity.Codec.cfgWord_le_length`, `Complexity.Codec.width_of_code`.
