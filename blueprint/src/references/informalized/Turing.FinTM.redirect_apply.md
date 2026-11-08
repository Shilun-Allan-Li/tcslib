<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.redirect_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redirection commutes with an action

**Claim.** Applying the redirected version of an action to the redirected image of a configuration gives the redirected image of the configuration obtained by applying the original action.

**Proof.** The only potential discrepancy in the two configurations is the register recording the last output bit. If the action emits a bit, the new last bit of the concatenated output is that bit; if it emits nothing, the previous last bit remains unchanged. Thus the last bit after applying the action is the emitted bit when present and otherwise the old last bit. The action's input-head movement, work-tape changes, and work-head movements are retained by redirection, while both redirected configurations have empty output. Their states consequently agree as well, by the definition of the redirected action and redirected state. All configuration components are equal, proving the claim.
