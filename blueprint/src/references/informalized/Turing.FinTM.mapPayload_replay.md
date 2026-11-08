<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapPayload_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay of a Captured Word

**Claim.** For every $j\leq |c.output|$, after $j$ steps from the payload-replay state the controller remains in that state, the input-head position remains $p$, the capture-head displacement is $j$, the output is $o$ followed by the first $j$ symbols of $c.output$, and the simulated machine's tapes and head positions are unchanged.

**Proof.** Proceed by induction on $j$. At $j=0$, the run has not moved, and the initial configuration is exactly the stated replay configuration; the empty prefix of $c.output$ contributes nothing to the output. For the successor step, assume the description holds at $j$ and suppose $j+1\leq |c.output|$. The captured tape at displacement $j$ contains the symbol $c.output[j]$, since the buffer stores the simulated output word and the index is within its length. Thus the replay transition reads that symbol, advances the capture head by one, leaves the input head fixed, and appends the symbol to the output. The transition is captured by `mapAction_apply`; `moveInputPos_zero` says that a zero input movement preserves $p$. Finally, adjoining the newly read symbol to the first $j$ symbols gives exactly the first $j+1$ symbols, establishing the claimed configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.mapAction_apply`, `Turing.moveInputPos_zero`.
