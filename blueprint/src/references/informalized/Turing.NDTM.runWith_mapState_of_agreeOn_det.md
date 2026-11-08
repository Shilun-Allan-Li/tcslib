<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_mapState_of_agreeOn_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Runs Under State Renaming

**Claim.** If the host transitions agree with the renamed deterministic source transitions on guarded states, then the host run under any choice word is the deterministic source run after the same number of steps, with its state renamed.

**Proof.** Regard the deterministic source machine as a nondeterministic machine whose transition ignores the choice bit. The transition agreement hypothesis is exactly the agreement required by the state-renaming theorem for nondeterministic runs. To check its guard condition, unfold the deterministic run as a nondeterministic run on the prefix of the choice word of length $u$: the deterministic-to-nondeterministic run identity (`Turing.MultiTapeTM.toNDTM_runWith`) gives this correspondence, and the prefix has length $u$ when $u<|w|$. The assumed guard condition therefore supplies the required good state at every such prefix. The state-renaming run theorem (`Turing.NDTM.runWith_mapState_of_agreeOn`) identifies the host run with the renamed run of the converted source machine. Finally, convert that source run back to the deterministic run using `Turing.MultiTapeTM.toNDTM_runWith`.

**Key facts.** `Turing.MultiTapeTM.toNDTM_runWith`, `Turing.NDTM.runWith_mapState_of_agreeOn`.
