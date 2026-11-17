<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_eq_fixChoice_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement with a Fixed-Choice Run

**Claim.** If, at every state encountered before the end of the fixed-choice run, the two transitions of the nondeterministic machine agree for every tape reading, then the run under the arbitrary choice word $w$ agrees with the run of the machine whose choice is fixed to $b$ for $|w|$ steps.

**Proof.** Regard the state embedding as the identity and call a state good when the two choice transitions agree there. For a good state, either choice in the nondeterministic machine produces the same action as the fixed-choice machine, since the two actions agree for every input and work-tape reading. The run-comparison theorem for transitions that agree on states encountered in the deterministic run (`Turing.NDTM.runWith_mapState_of_agreeOn_det`) therefore identifies the nondeterministic run under $w$ with the fixed-choice run for $|w|$ steps. The identity embedding leaves configurations unchanged, so this is the desired equality.

**Key facts.** `Turing.NDTM.runWith_mapState_of_agreeOn_det`.
