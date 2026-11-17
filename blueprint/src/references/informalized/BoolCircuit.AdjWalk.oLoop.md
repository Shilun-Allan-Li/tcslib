<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.oLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Scan Loop

**Claim.** Under the stated register bounds and loop conditions, the walk on the word of $d$ ones followed by zero either halts with the indicated answer when $i$ lies in the scanned interval, or reaches the prescribed postcondition when the scan has passed $i$.

**Proof.** Use induction on $d$, keeping the starting position $k$, the register values, and the target index in the induction statement. When $d=0$, the relation $W+d=V$ gives $W=V$. One loop step at state $oL$ sees equal loop and target registers, emits the terminal zero at position $k$, and proceeds to `done`; the emitted-bit specification gives the required answer if $i=k$, while the postcondition matches the updated registers. The register-bound invariant follows from the hypotheses. For the successor case, $W<V$, so the loop emits a one at position $k$. The emission fact (`Em.emit`) advances the position and updates the state while preserving the required register bounds. The append principle for emitted words (`Em.append`) separates this first one from the remaining scan. After that emission, the walk increments the scan register from $W$ to $W+1$ and continues in state $oL$. Apply the induction hypothesis with scan length $d$, starting position $k+1$, and current value $W+1$; the arithmetic hypotheses follow from $W+d+1=V$ and the original bounds. The resulting answer or terminal postcondition is transported through the register-update equality, completing the induction.

**Key facts.** `BoolCircuit.AdjWalk.gd_rg`, `BoolCircuit.AdjWalk.Em.step`, `BoolCircuit.AdjWalk.rg_1`, `BoolCircuit.AdjWalk.rg_3`, `BoolCircuit.AdjWalk.Em.emit`, `BoolCircuit.AdjWalk.Em.append`, `BoolCircuit.AdjWalk.upd_3`, `BoolCircuit.AdjWalk.Em.mono`.
