<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneSide_shiftInW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift-In Preserves Concatenation

**Claim.** Shifting in leaves the side word unchanged, whether the shift conditions hold or not.

**Proof.** If the shift conditions fail, the lists are unchanged, so their concatenation is unchanged. If they hold, the list at index $i-1$ is empty and the list at index $i$ is split into its first $2^{i-1}$ entries and the remaining entries. The shift places these pieces at indices $i-1$ and $i$, respectively. Their concatenation is therefore the original list at $i$, just as before; every other index is unchanged. The adjacent-index concatenation principle (`zoneSide_adjacent`) then gives equality of the full side words.

**Key facts.** `Turing.zoneSide_adjacent`.
