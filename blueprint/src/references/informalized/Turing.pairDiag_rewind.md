<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Rewind Pass

**Claim.** For every bit string $x$, output string $w$, and natural number $j\le |x|$, running the machine for $j+1$ steps from state $4$, with input head at position $j$ and output $w$, yields state $5$ with input head at position $1$ and output still $w$.

**Proof.** Proceed by induction on $j$. When $j=0$, the starting head is at the left boundary. One step takes the machine’s transition from state $4$ on no scanned symbol; this moves the head right to position $1$, changes the state to $5$, and emits nothing. Thus the output remains $w$. For the successor case, first take one step from state $4$ at position $j+1$. Since $j<|x|$, the head scans $x_j$ by the interior-position rule (`Turing.pairDiag_inner`). The transition takes the machine into state $4$ at position $j$, without changing the output. The induction hypothesis then rewinds from position $j$ to position $1$ in a further $j+1$ steps, preserving that output. Together these steps give the asserted run length and final configuration. The run equations used here say that a run of zero steps leaves its configuration unchanged and that a run of one additional step is obtained by applying one machine step (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_succ_eq_step`). Configurations with zero work tapes are equal once their states, input positions, and outputs agree (`Turing.Cfg.ext_zero_tapes`); the head moves right from the left boundary and left from any nonzero position according to the stated movement rules (`Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_neg_of_ne_left`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.Cfg.ext_zero_tapes`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_neg_of_ne_left`, `Turing.pairDiag_inner`.
