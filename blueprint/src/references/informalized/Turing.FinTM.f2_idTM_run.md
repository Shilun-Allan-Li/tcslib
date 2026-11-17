<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_idTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running the Identity Machine

**Claim.** For every $t\le |x|$, after $t$ steps the identity machine remains in its initial state, has its input head at position $t+1$, and has output $x.take\ t$.

**Proof.** Induct on $t$. At zero steps the initial configuration has the initial state, head position $1$, and empty output, which is the empty prefix. For the successor step, the induction hypothesis gives the state, head position, and output at time $t$. Since $t<|x|$, the next input symbol is $x_t$ (the input-symbol-at-position fact, `Turing.inputSymbolInner`). The identity machine stays in its state, advances the input head by one, and appends that symbol to the output. Thus the head is at $t+2$, and the output is $x.take(t+1)$ by the recursive description of list prefixes.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`.
