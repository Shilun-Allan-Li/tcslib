<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitRestore_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Restoration Phase

**Claim.** For every natural number $k$ and Boolean words $w,s$, there is a positive integer $t\le 2|s|+|w|+5$ such that the split-restoration machine from its scan configuration at position $0$ is not in state $(4,\mathrm{false})$ at any earlier time, and at time $t$ it is in the stated configuration with that state, input head at position $1$, the prescribed first-tape word, blank other tapes, zero work-tape heads, and empty output.

**Proof.** The restoration run lemma (`f2_splitRestore_run`) supplies a time $T\le 2|s|+|w|+5$ at which the run reaches the stated configuration in state $(4,\mathrm{false})$. That state is fixed: its transition is a zero-movement control action, so the control-action identity (`controlAction_apply`) together with `moveInputPos_zero` shows the whole configuration remains unchanged. The first-entry principle (`f2_catalogFirstEntry`) therefore yields a time $t\le T$ when this state is first reached, with no earlier occurrence. This first time is positive, since at time zero the scan configuration has first state coordinate $0$, whereas the target state's first coordinate is $4$; the zero-time run identity (`runFrom_zero`) makes this distinction explicit. Hence $0<t\le 2|s|+|w|+5$, as required.

**Key facts.** `Turing.FinTM.f2_splitRestore_run`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`, `Turing.FinTM.f2_catalogFirstEntry`, `Turing.MultiTapeTM.runFrom_zero`.
