<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_rawStrip_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying an input prefix

**Claim.** For every Boolean word $x$ and every $j\le|x|$, after $j$ steps the raw strip machine is in state $0$, has its input head at position $j+1$, has copied $x$'s length-$j$ prefix to its work tape, has its work head at $j$, and has empty output.

**Proof.** Induct on $j$. At $j=0$, the initial configuration agrees with the claimed empty-prefix configuration, component by component. For the successor step, the induction hypothesis gives the configuration after $j$ steps. Since $j<|x|$, the input symbol there is $x[j]$ (`inputSymbolInner`). The machine's transition in state $0$ writes this bit at work-head position $j$, moves both heads one place to the right, and emits nothing. The input head therefore reaches position $j+2$ (`moveInputPos_pos_of_ne_right`), and the work tape becomes the buffer for $(x.take\ j)++[x[j]]=x.take(j+1)$. The buffer update is exactly the append law (`bufferTape_append`); the work head and output then have the stated values by the transition definition.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
