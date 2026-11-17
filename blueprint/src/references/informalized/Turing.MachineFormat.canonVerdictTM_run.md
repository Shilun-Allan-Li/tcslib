<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonVerdictTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the canonical-bit verdict machine

**Claim.** Starting in the forward-pass state with words on the work tapes, after $2|w(i)|+3$ steps the verdict machine is halted and has output the single bit given by the last bit of $w(i)$, or $1$ when $w(i)$ is empty.

**Proof.** First run the underlying scan machine for $2|w(i)|+2$ steps. Its run theorem (`canonBitsTM_run`) says that it reaches the completed state carrying the scan result, with no earlier visit to any completed state. The verdict machine agrees with this scan machine on every forward- and backward-pass state, and the guard supplied to the state-mapping run theorem (`runFrom_mapState_of_agreeOn`) holds because the scan has not entered a completed state before that time. Consequently, after those steps the verdict machine is in the corresponding completed state with the same tape configuration. One further transition emits the stored Boolean and changes the state to the halting state. By definition, the scan result is the last bit of the word, defaulting to true for the empty word, so the output is precisely the claimed singleton.

**Key facts.** `Turing.MachineFormat.canonBitsTM_run`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
