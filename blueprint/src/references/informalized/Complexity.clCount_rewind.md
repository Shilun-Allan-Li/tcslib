<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding to the Origin

**Claim.** For every bit-list input, valid input-head position, bit list $w$, and $j\le |w|$, running the machine for $j+1$ steps from rewind control with work head at cell $j-1$, tape holding $w$, and empty output ends in return control, with work head at zero and the other data unchanged.

**Proof.** Induct on $j$. When $j=0$, the starting head position is $-1$; the machine's rewind transition moves it to zero and enters return control. The zero-step run law identifies the configuration before that transition, and the one-step run law relates the resulting run to the transition (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`). For the successor case, write the starting head position as the natural number $j$ viewed as an integer. Since $j<|w|$, the symbol at that cell exists and is $w[j]$. The rewind transition leaves the tape unchanged and moves the work head from $j$ to $j-1$, while preserving the input position and output; its input movement is zero (`Turing.moveInputPos_zero`). The run of $j+2$ steps therefore consists of this transition followed by the inductive run of $j+1$ steps from head position $j-1$. The induction hypothesis applies because $j\le |w|$, giving the return configuration at head position zero.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
