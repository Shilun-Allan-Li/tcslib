<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5NoFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing False Output Bits

**Claim.** The output after $T$ steps contains no false bit exactly when every transition prescribed by a snapshot at a time $t<T$ emits something other than false.

**Proof.** The output after $T$ steps is the concatenation, over times $t<T$, of the optional outputs prescribed by the corresponding snapshots (`clA5Run_output`). If some such transition emits `some false`, that false bit appears in the concatenated output, so the output is not false-free. Conversely, if the output contains false, membership in the flattened list gives a time $t<T$ whose optional emitted output contains false. It cannot be `none`, so it is `some b`; the contained bit forces $b=false$. Hence that transition emits `some false`, contradicting the condition that every such emission differs from `some false`.

**Key facts.** `Complexity.clA5Run_output`.
