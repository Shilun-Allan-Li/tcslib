<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/StateRenaming.lean :: Turing.Cfg.mapState_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Renaming and Action Application

**Claim.** Renaming the states of an action and a configuration before applying the action gives the same configuration as applying the original action and then renaming the resulting state.

**Proof.** The two configurations have the same state because both are obtained by mapping the action's successor state through the given function. Their input head positions agree since state renaming leaves the input movement and head position unchanged. For each work tape, the action and configuration's tape data and head positions are unchanged by renaming, so the resulting tape contents and head positions agree. Finally, the output is unchanged by renaming as well. Thus every configuration component agrees.
