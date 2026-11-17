<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.halted_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Persists for Longer Words

**Claim.** If every choice word of length exactly $n$ takes $M$ from $C$ to a halting configuration, then every choice word of length at least $n$ does so as well.

**Proof.** Take a word $w$ with length at least $n$, and split it into its first $n$ bits and the remaining suffix. The first part takes $M$ from $C$ to a halting configuration by hypothesis. The run on the concatenated word is the run on the first part followed by the run on the suffix (`runWith_append`). Once a configuration is halting, further choices leave it unchanged (`runWith_of_halt`), so the final configuration is still halting.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
