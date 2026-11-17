<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.foldl_vStepO_ok_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Persistence of invalidity

**Claim.** If a validation state starts with its first validity flag false, then folding the option-valued cell update over any finite list leaves that flag false.

**Proof.** Induct on the list, allowing the starting state to vary. For the empty list, folding changes nothing, so the flag remains false. For a list with first entry $o$ and tail $L$, the one-step update preserves the false flag by the fact that a false validity flag remains false under either option-valued update (`vStepO_ok_false`). Apply the induction hypothesis to the tail starting from this updated state; the flag is still false at the end.

**Key facts.** `Complexity.Codec.vStepO_ok_false`.
