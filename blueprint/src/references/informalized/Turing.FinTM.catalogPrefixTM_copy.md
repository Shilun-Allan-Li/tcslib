<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPrefixTM_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Copy Phase

**Claim.** For Boolean words $w,x$ and every $i\le |x|$, after $i$ steps from the configuration in state $|w|$, with input head at position $1$ and output $w$, the machine is still in state $|w|$, its input head is at position $i+1$, and its output is $w$ followed by the first $i$ symbols of $x$.

**Proof.** Proceed by induction on $i$. At $i=0$, the run has made no changes: the head is at position $1$ and the output is $w=w++x.take\,0$. For the successor step, assume the stated configuration after $i$ steps, with $i<|x|$. The input-symbol lemma says that the symbol at head position $i+1$ is $x_i$ (`inputSymbolInner`). Since the control state is $|w|$, the prefix-emitter transition outputs no work-tape change, emits that scanned bit, moves the input head right, and keeps the state at $|w|$. The rightward-movement lemma gives the new head position $i+2$ (`moveInputPos_pos_of_ne_right`); appending the emitted bit changes the output to $w++x.take(i+1)$. Equality of these configurations follows by checking state, head position, and output, which determine a zero-work-tape configuration (`Cfg.ext_zero_tapes`). The run recurrence identifies the $(i+1)$-step run with one step after the $i$-step run (`MultiTapeTM.runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
