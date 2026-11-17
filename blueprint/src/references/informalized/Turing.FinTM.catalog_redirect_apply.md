<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.catalog_redirect_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redirected Action Correspondence

**Claim.** Applying the redirected version of an action to the redirected configuration produces the redirected configuration of the result of applying the original action.

**Proof.** The redirected configuration records the original state and the most recent output bit in its state, preserves the input position and work tapes, and has an empty output tape. Applying the redirected action preserves the original action’s input movement and work-tape effects, emits nothing, and updates its recorded bit to the new output bit if one is produced, retaining the previous bit otherwise. Meanwhile, applying the original action appends its optional output bit to the output list; the last element of that list is exactly the new bit when present, and otherwise remains the previous last element. Thus the updated redirected state agrees on both sides. The input position, work tapes, and work-head positions also agree by the definitions of action application and redirection, and both redirected output tapes are empty. Extensionality of configurations then gives the result.
