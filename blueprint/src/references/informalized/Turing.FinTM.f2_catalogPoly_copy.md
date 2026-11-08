<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPoly_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy phase invariant

**Claim.** For each $i\le |x|$, after $i$ steps from the initial configuration the unary machine is in its copy state, with empty output, input-head position $i+1$, every work head at $i$, and every tape containing true exactly at positions $0$ through $i-1$.

**Proof.** Induct on $i$. At $i=0$, the initial configuration has input-head position $1$, all work heads at $0$, empty output, and blank tapes; the tape description agrees with the specified tape contents for parameter zero. For the successor step, the induction hypothesis gives the copy configuration at time $i$. Since $i<|x|$, the input-head position is strictly inside the word, so the input-symbol fact `inputSymbolInner` says the machine reads $x[i]$. The copy transition advances the input head and every work head, and writes true at the current work-head cell on every tape. The head-position formula for a rightward input move (`moveInputPos_pos_of_ne_right`) gives the new input position $i+2$. The tape update is exactly the passage from the interval of true cells $[0,i)$ to $[0,i+1)$, as recorded by `f2_catalogPolyTape_write`; output remains empty. The iteration identity `runFrom_succ_eq_step'` turns this one-step calculation into the induction step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.f2_catalogPolyTape_write`.
