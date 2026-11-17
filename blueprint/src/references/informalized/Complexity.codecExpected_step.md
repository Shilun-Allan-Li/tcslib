<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecExpected_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected encoding of a machine step

**Claim.** When the wired port values satisfy the codec guard, every codec bit's expected value under the action selected by the case equals its observed value in the machine's successor configuration.

**Proof.** The guard identifies the case with the configuration's actual state, input symbol, and work-tape symbols, and also gives the encoded input-head and work-head positions their required alignment (`Complexity.codecGuard_spec`). Hence the action selected from the case is exactly the machine transition action for this configuration: `Complexity.codecAction_apply` says that applying this action to the configuration gives one machine step. The action-encoding result (`Complexity.codecExpected_apply`) then identifies every expected bit with the observed bit after this action, provided the output is first replaced by the encoding of its summary. Finally, normalizing the output in this way does not change the observation of the successor step (`Complexity.codecObserve_step_normalize`). Combining these equalities gives the asserted agreement with the observed successor configuration.

**Key facts.** `Complexity.codecGuard_spec`, `Complexity.codecAction_apply`, `Complexity.codecExpected_apply`, `Complexity.codecObserve_step_normalize`.
