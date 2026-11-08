<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation for a Simulated Step

**Claim.** Under the stated head-position and blank-boundary assumptions, the prescribed run reaches the right-extension phase with the source state and the read table at coordinate $a+n$, with the enlarged encoded zone and boundary markers in the claimed stacks; the input position and encoded output are preserved.

**Proof.** Write $D$ for the encoded zone of $n$ blocks starting at $a$, $F$ for the unencoded zone of $n+1$ rows starting at $a-1$, and $R$ for the corresponding rows with left-neighbour head flags. The row at $a-1$ is blank: all heads lie at or to the right of $a$, and every tape is blank at $a-1$. The blank-row fact (`tapeRow_blank`) therefore identifies $F$ as one blank row followed by the rows in $D$. Also, the initial read table at $a-1$ is empty, since no head lies there or at its predecessor.

First, the growth-left phase adds one block of $k$ blank cells and moves the frontier from $z$ to $z-k$ (`sweep_grow_left_block`). The following step turns the scan around: the turn identity (`sweep_turn_right`) places the boundary marker on the left stack and puts the encoded rows on the right, using the decomposition of $F$ just established. The extra boundary marker is consumed on this turn; because $k>0$, dropping $k$ entries from its singleton list leaves the empty list.

The read phase now scans all rows of $F$. The one-pass sweep theorem (`sweep_run`) says that this scan updates the controller by folding `readVisit` over the rows and returns the rewritten rows, reversed onto the left stack. The fold calculation is exactly the row-reading identity (`read_zone`): the resulting controller table is `readState` at $a+n$, and the rows are $R$. The zone-length identity (`tapeZone_length`) gives $|F|=(n+1)k$, so this phase takes exactly that many steps and advances the frontier by that amount. At the end the work head sees the right boundary marker, by `sweepTape_read`; the machine changes to the right-extension state without changing the zipper (`sweepCfg_stay`). Combining these phase lengths yields $k+1+(n+1)k+1$, and the displayed stacks, frontier, input position, and output follow.

**Key facts.** `Turing.FinTM.tapeRow_blank`, `Turing.FinTM.sweep_grow_left_block`, `Turing.FinTM.sweep_turn_right`, `Turing.FinTM.sweep_run`, `Turing.FinTM.read_zone`, `Turing.FinTM.tapeZone_length`, `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepCfg_stay`.
