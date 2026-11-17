<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clInput_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Input Copying

**Claim.** For a Boolean word $x$ and $0\le j\le |x|$, after $j$ steps from the copier configuration with input head at position $1$, empty work tape, and work head at $0$, the machine is in its copying control with input head at position $j+1$, the first $j$ bits of $x$ copied onto the work tape, and work head at $j$.

**Proof.** Induct on $j$. At $j=0$, the claimed configuration is the starting configuration. For the successor step, the induction hypothesis places the input head at position $j+1$, where it reads $x_j$. The copier moves the input head right, writes that bit at the current work-head position $j$, moves the work head to $j+1$, and stays in its copying control. The tape update agrees with appending $x_j$ to the prefix of length $j$: the buffer-tape append identity (Turing.FinTM.bufferTape_append) identifies this append with writing at position $j$. The input-head movement has the claimed position by the right-move formula (Turing.moveInputPos_pos_of_ne_right). Thus the resulting configuration is the asserted one at index $j+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
