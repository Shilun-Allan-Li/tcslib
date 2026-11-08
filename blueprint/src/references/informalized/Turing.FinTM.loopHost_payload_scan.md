<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_payload_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload Tape Scan

**Claim.** Under the stated transition rule, if the payload tape stores $w$ and its head begins at $j-1$ for $j\le |w|$, then after $j+1$ steps the host is in phase $d$, with the specified other data unchanged and the payload head at $0$.

**Proof.** Use the left-scan principle `loop_scan_left` on the configurations indexed by the current distance from the left end. For each positive index $j$, the head scans position $j$, which contains a symbol because $j\le |w|$ (`bufferTape_nat`). By the assumed transition rule it moves left and stays in phase $s$. The frame update lemma `loopControl_apply` shows the other specified data remain fixed. At index zero the head is at $-1$, which is blank (`bufferTape_left`); the rule now moves it right to $0$ and enters phase $d$. Applying `loop_scan_left` yields the required $j+1$-step run, including the empty scan case.

**Key facts.** `Turing.FinTM.loop_scan_left`, `Turing.FinTM.loopFrame_payload`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.loopControl_apply`.
