<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordSkipTM_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement in the Successor Phase

**Claim.** Starting from a configuration in the successor phase, the record-and-skip machine run for any number of steps agrees with the successor-field machine run after renaming its state.

**Proof.** Embed each successor-phase state $q$ as the host state $(\text{true},q)$. In this phase the skip machine uses the successor-field machine as its phase component, and its transition is exactly the source transition with this state embedding applied. The embedding is injective, and every source state satisfies the guard condition because the chosen guard is always true. The run-agreement theorem for state embeddings therefore gives the claimed equality for every number of steps (\texttt{MultiTapeTM.runFrom\_mapState\_of\_agreeOn}).

**Key facts.** `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`.
