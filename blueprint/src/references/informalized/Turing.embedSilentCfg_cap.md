<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentCfg_cap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contents and head position of the buffer tape

**Claim.** When the buffer tape index is outside the embedding's image, its contents are the buffer for the prefix followed by the original output, and its head is at the length of that concatenated list.

**Proof.** Because the buffer tape index lies outside the image, the embedding assigns its contents and head position using the unselected-tape branches (`embedSlot_unselected`). The contents are therefore the buffer for the prefix concatenated with the original output, and the head is the integer length of that same list.

**Key facts.** `Turing.embedSlot_unselected`.
