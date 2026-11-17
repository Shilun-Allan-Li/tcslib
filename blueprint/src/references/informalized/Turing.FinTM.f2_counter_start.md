<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Initial Counter Steps

**Claim.** For every Boolean word $x$, every $i<|x|$, and every Boolean word $bs$, the one-step successors from the stated configurations in states $0$ and $1$ are equal.

**Proof.** The first configuration scans $x_i$: by the input-symbol calculation for a head at position $i+1$ ($\texttt{Turing.inputSymbolInner}$), its scanned symbol is $x_i$. The state-$1$ configuration at position $i+2$ scans the same symbol, directly from the definition of the input head. Thus both transitions read the same input bit; their work-tape reading is also the same, namely the symbol at position $0$ of the counter tape. The transition definitions reduce the two cases to a bump moving the input head right and a bump leaving it fixed. Split according to whether the counter tape contains true at position $0$. In either case the resulting state, work tape, work-tape head, and output agree. The input positions agree because moving right from position $i+1$ gives $i+2$ ($\texttt{Turing.moveInputPos_pos_of_ne_right}$), while a zero move preserves position $i+2$ ($\texttt{Turing.moveInputPos_zero}$); the hypothesis $i<|x|$ ensures the rightward move is not at the boundary.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_zero`.
