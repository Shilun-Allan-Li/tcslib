<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.codeAt_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Sequence at Its Initial Position

**Claim.** Every finite instruction sequence is the initial segment of itself when read from position zero.

**Proof.** At position zero, dropping zero instructions from the list leaves the list unchanged. A list is a prefix of itself by reflexivity of the prefix relation, so the sequence is the initial segment of itself.
