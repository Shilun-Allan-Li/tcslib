<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_compare_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparator Rewind

**Claim.** For every $j\le\max(|u|,|v|)$, starting in the rewind phase with both word heads at displacement $j-1$ and register $b$, the comparator reaches the return phase after $j+1$ steps, with both heads at zero and the register unchanged.

**Proof.** Proceed by induction on $j$. For $j=0$, the initial displacement is $-1$. Both tapes are blank there, by the fact that a buffer tape reads blank at position $-1$ (`Turing.FinTM.bufferTape_left`). The rewind transition therefore enters the return phase and moves both heads forward once, from $-1$ to $0$, preserving the register. This is the required one step. For the successor case, the bound implies $j<\max(|u|,|v|)$, so the two tapes are not both blank at index $j$ (`Turing.FinTM.emitter_compare_nonblank`). At displacement $j$, the rewind transition stays in the rewind phase, moves both heads one position backward, and leaves the register unchanged. Since $(j+1)-1=j$, this first step produces the induction hypothesis's starting configuration at displacement $j-1$. The remaining $j+1$ steps complete the rewind by induction, giving $(j+1)+1$ steps in total. The input head and the other configuration data are preserved throughout.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.emitter_compare_nonblank`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
