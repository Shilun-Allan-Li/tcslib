<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_rewind_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single Rewind-Phase Transition

**Claim.** For $i<|x|$, one step from state $1$ with input head at position $i+1$, the full copy of $x$ on the work tape, and work head at $|x|$ reaches state $1$ with input head at position $i$, preserving the work tape, work-head position, and empty output.

**Proof.** At input position $i+1$, the machine reads $x_i$ (`inputSymbolInner`). Its state-$1$ transition moves the input head one position left, from $i+1$ to $i$; the left-move position rule supplies this value (`moveInputPos_neg_of_ne_left`). The transition leaves the work tape and work-head position unchanged and emits nothing, while retaining state $1$.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_neg_of_ne_left`.
