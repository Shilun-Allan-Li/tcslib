<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStepPair_side -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired Shift Preserves Side Words

**Claim.** The paired shift leaves unchanged the concatenation of all left zone words and also the concatenation of all right zone words.

**Proof.** The paired shift changes the left side by the outward word shift and the right side by the inward word shift. The total concatenation of a side is invariant under each respective redistribution: outward shifting preserves it (`zoneSide_shiftOutW`), and inward shifting preserves it (`zoneSide_shiftInW`). Applying these facts to the two sides gives the stated equalities.

**Key facts.** `Turing.zoneSide_shiftOutW`, `Turing.zoneSide_shiftInW`.
