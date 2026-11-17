<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Rewind

**Claim.** For every Boolean list $x$, valid input-head position $p$, and Boolean list $bs$, after $j+1$ steps from state $2$ with work-tape head at $j-1$, the machine is in state $0$ with the same input position, head at $0$, unchanged tape, and empty output, for every $j\le |bs|$.

**Proof.** Induct on $j$. When $j=0$, the head starts at $-1$ and the first state-$2$ transition returns it to $0$, producing state $0$ while preserving the tape, input position, and empty output. For the successor case, the head starts at position $j$, where it reads $bs[j]$ because $j<|bs|$. The state-$2$ transition leaves the other configuration data unchanged and moves the head one cell left, from $j$ to $j-1$. The input position stays fixed by the zero-movement identity (`moveInputPos_zero`). Reindexing the integer head positions shows that this transition supplies the initial configuration for the induction hypothesis; the run split after one step (`runFrom_succ_eq_step`) then gives the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
