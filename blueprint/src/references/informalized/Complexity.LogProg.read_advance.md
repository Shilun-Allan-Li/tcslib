<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One reading advance

**Claim.** If $k<\min(i,|x|)$, the reading machine can advance from the initial reading phase with tape $s$ holding the binary representation of $k$ and input-head position $k+1$ to that phase with tape $s$ holding the binary representation of $k+1$ and input-head position $k+2$, while every earlier configuration lies in the read frame of $c$.

**Proof.** Use the reading-equality run (`Complexity.LogProg.read_eq`) to compare the current counter $k$ with $i$. Since $k<i$, it reaches the negative-comparison phase, with every configuration before that endpoint in the read frame. One more step enters the increment phase: the input-symbol identity (`Complexity.LogProg.inSym_succ`) identifies the symbol read at position $k+1$ with the input symbol at index $k$, and the rightward-position formula (`Complexity.LogProg.moveInputPos_pos_val`) gives input-head position $k+2$.

The counter-increment run (`Complexity.LogProg.inc_run`) now advances tape $s$ from the binary representation of $k$ to that of $k+1$, ending in the initial comparison phase. Its intermediate configurations update only the relevant register and keep the register head within the stated bound for the binary representation of $k+1$. The run-concatenation identity (`Complexity.LogProg.rrun_add`) joins the comparison, the single input-reading step, and the increment into one run. For the frame condition, times in the initial comparison segment are covered by `read_eq`; the transition into the increment phase is covered by `readFrame_at`; and times during the increment segment are covered by `readFrame_reg`. The increment's head bound transfers to the required bound using monotonicity of binary-representation length (`Complexity.LogProg.length_bits_mono`), since $k+1\le |x|+1$.

**Key facts.** `Complexity.LogProg.read_eq`, `Complexity.LogProg.inSym_succ`, `Complexity.LogProg.moveInputPos_pos_val`, `Complexity.LogProg.inc_run`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.readFrame_at`, `Complexity.LogProg.readFrame_reg`, `Complexity.LogProg.length_bits_mono`.
