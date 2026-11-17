<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitRestore_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split Restoration Run

**Claim.** For every natural number $k$ and Boolean words $w,s$, there is a time $t\le 2|s|+|w|+5$ at which the split-restoration machine, started in its scan configuration at position $0$, reaches the configuration with state $(4,\mathrm{false})$, input head at position $1$, first work tape containing $s$ with true appended if $|s|\le |w|$ and otherwise $s$, all other work tapes blank, all work-tape heads at $0$, and empty output.

**Proof.** Put $s'=f2\_splitStep(w,s)$, the word that equals $s$ with a final true appended when $|s|\le |w|$, and equals $s$ otherwise. In particular, $|s|\le |s'|$. The scan phase advances the input head through the word while maintaining its scan configuration: after $|s|$ steps it is at position $|s|$. One further step enters the clean configuration in state $(1,\mathrm{false})$, with the first work tape set to $s'$, the scratch tape prepared for restoration, and the work-tape heads at the positions specified by that clean configuration. Thus, after $|s|+1$ steps the machine is in this clean configuration (using the scan and append facts `f2_splitRestore_scan` and `f2_splitRestore_append`).

From there, the rewind phase takes $|s|+1$ steps to reach state $(2,\mathrm{false})$ with the work-tape head restored to $0$ (`f2_splitRestore_rewind`). The transition out of state $(2,\mathrm{false})$ moves the input head one position left and enters state $(3,\mathrm{false})$. In state $(3,\mathrm{false})$, each step continues left while the input head reads a symbol; upon reaching the left boundary, the machine moves right and enters $(4,\mathrm{false})$. The catalog rewind fact guarantees that this final scan reaches input position $1$ in at most the starting input position plus two steps (`f2_catalogRewind`).

Combining these phases with the composition law for runs (`runFrom_add`) gives a total time $t=(|s|+1)+(|s|+1)+r$, where $r$ is the final rewind duration. The clean configuration has input position at most $|w|+1$, so the rewind bound gives $r\le |w|+3$; hence $t\le 2|s|+|w|+5$. The resulting configuration has the required state and input position. Its work tapes, head positions, and output agree with the stated target configuration by the clean and rewind descriptions and the definition of the target word.

**Key facts.** `Turing.FinTM.f2_splitRestore_scan`, `Turing.FinTM.f2_splitRestore_append`, `Turing.FinTM.f2_splitRestore_rewind`, `Turing.FinTM.f2_catalogRewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
