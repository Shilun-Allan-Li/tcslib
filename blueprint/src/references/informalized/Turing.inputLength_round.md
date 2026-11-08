<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLength_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Input-Length Counting Round

**Claim.** Under the stated phase, position, digit, and tape hypotheses, after $2p+3$ steps the machine stores the digits of $n+1$ over a segment of length $p+1$, has returned its work head to its original position, and has moved the input head one clamped step to the right; throughout the round the work head stays between one cell left and $p$ cells right of its starting position.

**Proof.** Write $w=(n+1).bits$, let $ip$ be the input position after one rightward move, and describe the forward scan configurations by $F(r)$: the machine is in carry phase, has buffered the first $r$ symbols of $w$, and its work head is at offset $r$. Describe the return configurations by $R(r)$: the machine is in back phase with the full $p+1$-symbol buffer and its head at offset $r-1$. Let $D$ be the final count configuration with that buffer and head at offset zero.

The charge lemma (`Turing.inputLength_charge`) gives $p<|w|$, and the old digit description gives $p\le |n.bits|$. The initial transition enters $F(0)$: the input symbol is the $n$th symbol, and the transition moves right into carry phase without changing the tape. At each offset $r<p$, the old tape contains a one and the new digits have a zero there, so the machine writes that zero and advances, taking $F(r)$ to $F(r+1)$. At offset $p$, the old digit is not one and the new digit is one; the machine writes it and turns left, taking $F(p)$ to $R(p)$. These tape reads are justified by the buffer-tape evaluation facts (`Turing.FinTM.bufferTape_nat` and `Turing.FinTM.bufferTape_left`) and the given agreement of the old tape with the old digits. The write transition behavior is supplied by `Turing.inputLength_write`.

During the return scan, the digits at offsets below $p$ are zero. The machine moves left without writing, so each $R(r+1)$ advances to $R(r)$. At offset $-1$ it reads blank, moves right, and enters count phase, producing $D$. The blank read follows from the left-end buffer fact. The successor-step identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) iterates these transitions: after $r+1$ steps the machine is in $F(r)$, and after $p+2+r$ steps it is in $R(p-r)$. Thus after $2p+3$ steps it is in $D$, with the desired stored digits and head position. The input head has moved right once, while the work head returns to its original position by the specified forward and backward offsets.

For every intermediate time, divide into the initial time, the forward scan, the backward scan, and the final step. In the forward phase the work-head offset ranges from $0$ to $p$; in the backward phase it ranges from $p-1$ down to $-1$; the endpoints satisfy the same bounds. This proves the claimed head bounds.

**Key facts.** `Turing.inputLength_charge`, `Turing.FinTM.bufferTape_nat`, `Turing.inputLength_write`, `Turing.FinTM.bufferTape_left`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
