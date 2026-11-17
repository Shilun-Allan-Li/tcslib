<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.rawStrip_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Copying Phase

**Claim.** For $j\le |x|$, after $j$ steps the raw marker-stripping machine is in state $0$, has copied the first $j$ bits of $x$ to its work tape, has input-head position $j+1$ and work-head position $j$, and has emitted no output.

**Proof.** Induct on $j$. At $j=0$, the initial configuration has state $0$, both head positions at their initial positions, an empty work tape, and no output, which is exactly the asserted configuration with the empty prefix copied. For the successor step, assume the asserted configuration after $j$ steps and use the successor-run law (`runFrom_succ_eq_step'`). Since $j<|x|$, the input head reads the $j$th bit (`inputSymbolInner`). The machine writes that bit at the current work-head position and advances both heads by one (`moveInputPos_pos_of_ne_right` for the input head; the machine transition specifies the work-head movement). Appending the bit to the copied prefix updates the work-tape contents at precisely position $j$ (`bufferTape_append`), so the resulting configuration has copied $x.take(j+1)$, heads at positions $j+2$ and $j+1$, unchanged state $0$, and still empty output.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
