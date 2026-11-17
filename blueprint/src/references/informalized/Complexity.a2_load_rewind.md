<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_load_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind to the borrow phase

**Claim.** For binary input $x$, input-head position $p$, binary word $u$, and $j\le|u|$, the countdown machine started in its startup state with work tape $u$ and head at $j-1$ reaches the borrow phase after exactly $j+1$ steps, with head at $0$, unchanged tape and input position, and empty output.

**Proof.** Induct on $j$. When $j=0$, the work head starts at $-1$, where the buffered tape has no symbol (`bufferTape_left`). The startup transition therefore enters the borrow phase, moves the work head to $0$, and leaves the input position, tape, and output unchanged; this is exactly one step. For the successor case, first examine the startup configuration with head at $(j+1)-1=j$. Since $j<|u|$, the tape there contains the $j$th symbol (`bufferTape_nat`). One startup transition leaves the state and input position unchanged and moves the work head left, producing the startup configuration with head at $j-1$. The induction hypothesis then applies and takes $j+1$ further steps to the borrow phase. Together these give $(j+1)+1$ steps, with the claimed final configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
