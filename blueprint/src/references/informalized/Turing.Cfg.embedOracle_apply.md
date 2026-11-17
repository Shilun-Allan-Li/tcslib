<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.Cfg.embedOracle_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding Commutes with Applying an Action

**Claim.** Applying the state-renamed, extended action to the embedded configuration gives the embedding of the configuration obtained by applying the original action.

**Proof.** Compare the two configurations field by field. Their states agree because renaming a successor state by the left inclusion and then embedding the resulting state has the same effect as applying the left inclusion to the original successor state. Their input-head positions agree because the action and embedding leave the input-position calculation unchanged. For each work-tape index $i$, split according to whether $i<k$. In the first case, the extended action and the embedded configuration use the original tape and head position, so both sides perform the same write, movement, and update. In the second case, the added tape is blank with head at zero, and the extended action does nothing to it; both sides therefore leave that tape blank and its head at zero. Finally, both output fields append the same action output to the original output. Equality of all five fields proves the configurations equal.
