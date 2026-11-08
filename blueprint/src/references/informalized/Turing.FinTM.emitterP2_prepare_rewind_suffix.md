<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_prepare_rewind_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Suffix Head

**Claim.** For every $j\le |v|$, the preparation machine starting in phase $5$ with suffix tape $v$ and suffix head at displacement $j-1$ reaches phase $6$ after $j+1$ steps with that head at zero, preserving the words, flag, and input-head position.

**Proof.** We use induction on $j$. For $j=0$, the suffix head is at $-1$, so the suffix tape is blank there by `bufferTape_left`. In phase $5$, this makes the machine enter phase $6$ and move the suffix head one step right, reaching the stated frame in one step. The input head stays fixed because this transition does not move it.

Now suppose $j+1\le |v|$. At suffix-head position $j$, the tape contains the $j$th symbol of $v$, by `bufferTape_nat` and the bound. The phase-$5$ transition sees a symbol and moves the suffix head left one position, leaving the tape and the other frame data unchanged. The machine is again in phase $5$, now at displacement $j-1$. Apply the induction hypothesis to this configuration, and combine its $j+1$ steps with the initial step using `runFrom_succ_eq_step`. This yields the claimed total of $j+2$ steps.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
