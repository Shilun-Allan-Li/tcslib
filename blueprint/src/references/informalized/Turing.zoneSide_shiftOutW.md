<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneSide_shiftOutW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift-Out Preserves Concatenation

**Claim.** Shifting out leaves the side word unchanged, both when its length and room conditions hold and when they fail.

**Proof.** If the shift conditions fail, no list changes. When they hold, the list at index $i-1$ is split into its first $2^{i-1}$ entries and its remainder. The first piece is placed at index $i-1$; the remainder is concatenated with the original list at index $i$. Consequently, the concatenation of the two adjacent lists is unchanged. All other lists stay fixed, so the adjacent-index concatenation principle (`zoneSide_adjacent`) yields equality of the full side words.

**Key facts.** `Turing.zoneSide_adjacent`.
