# Clock-capture first-halt reuse proposal

Gate 122 leaves `clockStageCfg_captures` held on the carrier mismatch
between the raw clock configuration and the bundled masked and
oblivious machines. The proof proposes four non-simp field equations
in ObliviousSchedule, next to the two machine definitions.

* `maskedClock_k` and `maskedClock_State` give the witness tape
  count and state type.
* `obliviousSchedule_k` gives the witness tape count plus three.
  `obliviousSchedule_State` gives `OblPhase W.State a`.

The transported header explicitly passes the raw result to the
bundled carrier. Lean proves the complete original and revised
propositions equal by reflexivity. The new proof invokes
`MultiTapeTM.exists_first_halt` and carries the entire endpoint and
its earlier liveness to the existing clock-run lemma.

The full producer and consumer modules compile at 967bc00f00637312676f438c7f61b14219fa943b.
The complete target proof passed with seven active opaque definitions
and standard axioms. All fourteen control goals closed natively and
failed under the seal. The two direct callers each use
`simp only [id_eq] at hclock` to normalize the transported equation
before their existing rewrites. The native owner chain rebuilds
ObliviousSchedule, ObliviousCandidate, ObliviousSetup, ObliviousLedger
and Oblivious in that order. It is a scoped proposal check.

The initial consumer test showed that the old rewrite scripts needed
the normalization, despite equality of the propositions. The
explicit-cast alternative also failed the selected proof seal. Those
diagnostics remain in history. The proposed patch uses the checked
transport and the two normalization lines. START-HERE §2 reserves
the four new public equations and the literal-header change for
Seyoon's ruling.
