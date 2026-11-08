<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogRewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded input-head rewind

**Claim.** Under the stated transition rules, every configuration in state $s$ can be brought to state $d$ at input-head position $1$ within its current head position plus $2$ steps, without changing its other components.

**Proof.** Let the initial configuration be $c$. Its first transition is determined by the rule for state $s$: it moves left, enters state $t$, and leaves the other components unchanged. The control-action application rule (\texttt{Turing.FinTM.controlAction_apply}) identifies this resulting configuration. A left move changes the head position from $p$ to $p-1$ (\texttt{Turing.FinTM.moveInputPos_neg_val}); in particular the new position is at most the input length, so it is on an input cell or the left boundary. Now apply the scanning rewind lemma (\texttt{Turing.FinTM.rewind_scan}) from this configuration: in state $t$ the machine moves left across each input symbol, then moves right upon reaching the blank cell, arriving at position $1$ and state $d$ without changing other components. Decomposing the run into the initial transition followed by this scan (\texttt{Turing.MultiTapeTM.runFrom_add}) gives a total of one plus the scan length, namely $1+((p-1)+1)=p+1$, which is within the asserted bound $p+2$.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.rewind_scan`, `Turing.MultiTapeTM.runFrom_add`.
