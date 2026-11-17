<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonParseFront -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Parser Front End

**Claim.** For every machine format $F$, there is a finite Boolean Turing machine with at least four work tapes, an entry state, an injectively indexed family of verdict states, and a linear time bound. On each input it reaches one verdict state with empty output and no earlier visit to any verdict state; a false verdict means decoding falls back, while a true verdict certifies a canonical header and sufficient remaining length, with the specified input-head position and canonical ready words on tapes other than tape one.

**Proof.** Begin with the checked-front machine from `Turing.MachineFormat.exists_canonCheckedFront`. It has at least four tapes and reaches an exit labeled by an optional Boolean verdict, with no earlier visit to any such exit. Its false-or-unknown verdict implies fallback decoding; its true verdict supplies the canonical header bits, the guard-length bound, the input-head position, and the ready tape contents. Apply `Turing.MachineFormat.canonExitDispatch` to replace these optional-verdict exits by a fresh machine whose exit states are indexed injectively by ordinary Booleans. The dispatch construction takes one additional step after the checked-front run, preserves the configuration data, and ensures that the selected exit state is not reached earlier. Set the new verdict to true exactly when the old verdict is `some true`; otherwise set it false. In the false case, the old verdict was not `some true`, so the checked-front implication gives fallback decoding. In the true case, its certificate applies directly. The additional step changes the linear bound only by a constant factor (indeed the proof uses the bound with coefficient increased by one), so the required linear-time estimate follows.

**Key facts.** `Turing.MachineFormat.exists_canonCheckedFront`, `Turing.MachineFormat.canonExitDispatch`.
