<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clInput_backward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Input Head

**Claim.** For finite Boolean words $x,w$ and $j\le |x|$, the copier started in state $1$ with input head at position $j$ and work head at $j-1$, work tape storing $w$, and empty output reaches after $j+1$ steps state $2$, input head at position $1$, work head at $0$, with the tape still storing $w$ and output empty.

**Proof.** Induct on $j$. When $j=0$, one step from state $1$ reads the left boundary of the input and enters state $2`; the input head and work head remain at their stated positions, and neither the tape nor output is changed. For the successor case, the input head is at position $j+1$, so it reads the $j$th bit of $x$. The copier's transition in state $1$ moves the input head one place left, leaves the work-tape contents unchanged, and moves the work head one place left. Hence this single step produces exactly the configuration used by the induction hypothesis at index $j$. Decomposing the run of $j+2$ steps into this first step followed by the $j+1$-step run supplied by induction yields the claimed return configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.inputSymbolInner`, `Turing.FinTM.moveInputPos_neg_val`.
