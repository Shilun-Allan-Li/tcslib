<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_erase_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Scan of the Eraser

**Claim.** For every $j\le |u|$, after $j$ steps the eraser remains in state $0$ with tape $u$, head displacement $j$, unchanged input, and empty output.

**Proof.** Induct on $j$. At zero steps the configuration is the specified starting configuration. For the successor step, the induction hypothesis identifies the current configuration as state $0$ with tape $u$ and head at $j$. Since $j<|u|$, the scanned symbol is the $(j+1)$st symbol of $u$ (`Turing.FinTM.bufferTape_nat`). The state-$0$ scan transition leaves the symbol and input head unchanged, emits nothing, keeps the machine in state $0$, and advances the work head by one. This gives the claimed configuration at displacement $j+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
