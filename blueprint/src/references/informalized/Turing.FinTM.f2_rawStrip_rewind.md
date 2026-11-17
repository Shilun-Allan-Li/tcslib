<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_rawStrip_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw Strip Rewind

**Claim.** For Boolean words $x,a$, a position $i\le |x|$, and each $j\le |a|$, the raw strip machine started in state $2$ with work tape $a$, head at $j-1$, and empty output reaches state $3$ with head at $0$ and unchanged tape and output after $j+1$ steps.

**Proof.** Induct on $j$. When $j=0$, the head begins at $-1$. The first transition sees the blank cell to the left of the tape and moves into state $3$ while leaving the head at $0$; the run laws `Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_succ_eq_step` express this initial configuration followed by that step. The blank reading is justified by `Turing.FinTM.bufferTape_left`, and the head stays put in this transition by `Turing.moveInputPos_zero`. For the successor case, the starting head position $(j+1)-1$ simplifies to $j$. Since $j<|a|$, the machine reads the $j$th tape entry and moves one cell left, entering state $2$ with head at $j-1$, with tape and output unchanged. This one-step reduction is the explicit transition calculation; the successor run law (`Turing.MultiTapeTM.runFrom_succ_eq_step`) then reduces the remaining $j+1$ steps to the induction hypothesis. The symbol at position $j$ is identified using `Turing.FinTM.bufferTape_nat`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
