<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_rawStrip_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw Strip Replay

**Claim.** For Boolean words $x,a$, a position $i\le |x|$, and each $j\le |a|$, the raw strip machine started in state $3$ with work tape $a$, head at $0$, and empty output is after $j$ steps in state $3$, with head at $j$ and output $a.take j$.

**Proof.** Induct on $j$. At $j=0$, the initial configuration already has state $3$, head at $0$, and output the empty prefix. For the successor step, assume the claimed configuration after $j$ steps, where the bound on $j+1$ ensures that the tape contains an entry at position $j$. The run successor law (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) reduces the next configuration to one machine step from this inductive configuration. The transition reads the $j$th tape entry, advances the work head by one, preserves state $3$, and appends that entry to the output; the tape itself is unchanged. The buffer lookup identity (`Turing.FinTM.bufferTape_nat`) identifies the symbol read with $a[j]$, and the list-prefix successor identity gives $a.take j ++ [a[j]]=a.take(j+1)$. The input head does not move, by the zero-movement fact (`Turing.moveInputPos_zero`). These component equalities establish the claimed configuration at $j+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
