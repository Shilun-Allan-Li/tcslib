<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFill_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Constant-Fill Machine

**Claim.** Starting with the fill machine running at input position $i+1$, with output $out$ and no work tapes, after $|x|-i+1$ steps it is halted at the right boundary and its output is $out$ followed by $|x|-i$ copies of $b$.

**Proof.** Induct on the number $|x|-i$ of input symbols remaining, generalizing the starting position and output. If none remain, then $i=|x|$. The machine takes one step while reading the right boundary: its transition halts without adding an output symbol. The configuration is therefore halted at the boundary with output still $out$. If $r+1$ symbols remain, then $i<|x|$, so the input head reads the symbol $x[i]$. On any input symbol, the machine outputs $b$, stays in its running state, and moves the head one position right. After this first step the head is at $(i+1)+1$, and the output is $out++[b]$. There are now $r$ symbols remaining, so the induction hypothesis applies and says that the remaining run halts at the boundary with output $(out++[b])$ followed by $r$ copies of $b$. By the definition of list replication, this is $out$ followed by $r+1=|x|-i$ copies of $b$.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
