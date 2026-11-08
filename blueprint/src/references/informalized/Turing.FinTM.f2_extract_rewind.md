<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extract_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Work Tape Head

**Claim.** For every $j\le |a|$, running the extractor machine for $j+1$ steps from state $0$, input position $i$, tape $a$, head position $j-1$, and empty output reaches state $1$ at input position $i$, with the work-tape head at $0$ and output still empty.

**Proof.** Induct on $j$. When $j=0$, the head starts at position $-1$, where the tape is blank. The state-$0$ transition therefore moves the work head one position right and enters state $1$, without changing the input position or output. For the successor case, start with head position $(j+1)-1=j$. Since $j<|a|$, the tape contains $a_j$ there. In state $0$, the machine sees a symbol and moves the work head left, remaining in state $0$; it makes no other change. The remaining $j+1$ steps are exactly the induction run from head position $j-1$. The induction hypothesis gives the stated configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
