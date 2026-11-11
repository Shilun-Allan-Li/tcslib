<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPrefixTM_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copied catalog prefix

**Claim.** For Boolean words $w,x$ and every $i\le |x|$, after $i$ steps from state $|w|$, input-head position $1$, and output $w$, the machine is in state $|w|$, at position $i+1$, with output $w$ followed by the first $i$ symbols of $x$.

**Proof.** Proceed by induction on $i$. At $i=0$, the claimed configuration is the initial configuration for this copying phase. For the successor step, assume the description holds after $i$ steps. Since $i<|x|$, the input head is on the symbol $x_i$ (the input-symbol fact `Turing.inputSymbolInner` says exactly this when the head position is $i+1$). In state $|w|$, the machine emits that symbol, stays in the same state, and moves right. The right-move rule `Turing.moveInputPos_pos_of_ne_right` gives the new position $i+2$; the output is the previous prefix followed by $x_i$, which is the prefix of length $i+1$. These equalities identify the configurations using zero-tape extensionality (`Turing.Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
