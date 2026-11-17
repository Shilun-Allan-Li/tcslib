<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_take_payload -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a payload prefix

**Claim.** If $x=p b$ and $j\le\min(m,|b|)$, then after $j$ steps from the specified state $3$ configuration, the extractor remains in state $3$, advances the input head by $j$, leaves the unary work-tape content unchanged, moves its work head to $m-j-1$, and outputs the first $j$ bits of $b$.

**Proof.** Induct on $j$. At $j=0$, the machine is in its initial configuration for this assertion: the input head is at $|p|$, the work head at $m-1$, and the output is empty. For the successor step, the induction hypothesis describes the configuration after $j$ steps. Since $j<|b|$, the next input symbol at position $|p|+j$ is the bit $b_j$; this follows from $x=p b$ and the list indexing rule. The work head is still on a cell containing $1$, since $j<m$, so in state $3$ the machine copies that input bit to the output, advances the input head, and moves its work head one cell left. The input-symbol fact is read from the configuration by `Complexity.tmsat_take_read`; the one-step run is supplied by `Turing.MultiTapeTM.runFrom_succ_eq_step'`, and the head advance is valid by `Turing.moveInputPos_pos_of_ne_right`. The work tape itself is unchanged. The output becomes the first $j+1$ bits of $b$, while the work-head position becomes $m-(j+1)-1$, as required.

**Key facts.** `Complexity.tmsat_take_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_pos_of_ne_right`.
