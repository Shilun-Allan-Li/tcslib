<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairDup_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intermediate State of the Doubling Pass

**Claim.** For each $j\le |x|$, after $2j$ steps the duplicator is in its scanning state at input position $j$, and its output is the list of the first $j$ input bits, each written twice.

**Proof.** Induct on $j$. At $j=0$, the initial configuration has the scanning state, input position zero, and empty output, as required. For the successor step, assume the claim at $j$ and use the run-successor identity twice to examine the next two transitions (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). The scanning configuration reads the $j$th bit of the input (`Turing.FinTM.scanCfg_read`). Its first transition appends that bit and switches to the intermediate state; its next transition appends the same bit again and returns to the scanning state with the input head advanced one position. The resulting output is exactly the doubled list of the first $j+1$ bits, by the list take-and-append identity. The head movement is justified by the fact that the head is not at the right boundary (`Turing.moveInputPos_pos_of_ne_right`). Equality of the resulting configurations follows by comparing state, position, and output, since there are no work tapes (`Turing.Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
