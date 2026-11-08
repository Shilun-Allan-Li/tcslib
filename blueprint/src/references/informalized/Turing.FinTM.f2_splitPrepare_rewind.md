<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitPrepare_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation Rewind

**Claim.** For every natural number $k$, Boolean words $w,s$, and natural number $j\le |s|$, starting from the specified ready configuration in state $1$ with first work-tape head at $j-1$, the preparation machine reaches the specified ready configuration in state $2$ with all work-tape heads at zero after $j+1$ steps.

**Proof.** Induct on $j$. When $j=0$, the first work-tape head is at $-1$, so it reads blank by the negative-position property of the buffer tape (`bufferTape_left`). The state-$1$ transition therefore moves the relevant heads right, enters state $2$, and leaves the other configuration data unchanged; the run identities for zero and successor times (`runFrom_zero`, `runFrom_succ_eq_step`) reduce this to checking that single step. For the successor case, assume $j<|s|$. The head position $(j+1)-1$ equals $j$, where the first work tape contains the $j$th symbol of $s$, by the natural-position buffer identity (`bufferTape_nat`). In state $1$ with a symbol under that head, the transition moves the work-tape heads one place left and keeps the machine in state $1$. Thus one step from head position $j$ gives the induction configuration with head position $j-1$. The successor run identity reduces the claimed $j+2$-step run to this step followed by the induction hypothesis, yielding state $2$ and head position zero.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
