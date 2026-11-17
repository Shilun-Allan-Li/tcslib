<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_compare_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Comparator Scan

**Claim.** For each $j\le\max(|u|,|v|)$, after $j$ steps the comparator is in its scan phase, its register records whether the length-$j$ prefixes of $u$ and $v$ agree, and both word heads are at displacement $j$.

**Proof.** Induct on $j$. At zero steps the machine is in the specified initial scan configuration, and the two empty prefixes agree. For the successor step, the induction hypothesis gives the configuration after $j$ steps. The bound on $j+1$ implies $j<\max(|u|,|v|)$, so the two words are not both blank at index $j$ (`Turing.FinTM.emitter_compare_nonblank`). The tape symbols read at displacement $j$ are precisely the optional entries $u[j]? ,v[j]? $ (`Turing.FinTM.bufferTape_nat`). Thus the scan transition advances both heads and updates the register by conjoining its previous equality record with equality of these entries. The characterization of equal extended prefixes (`Turing.FinTM.emitter_take_succ_eq`) says exactly that this conjunction records whether the prefixes of length $j+1$ agree. The input head and tape contents do not change; hence the asserted configuration holds after $j+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.emitter_compare_nonblank`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.emitter_take_succ_eq`, `Turing.moveInputPos_zero`.
