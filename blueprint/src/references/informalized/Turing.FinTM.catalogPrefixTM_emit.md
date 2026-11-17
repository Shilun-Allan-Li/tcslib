<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPrefixTM_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Emission Phase

**Claim.** For Boolean words $w,x$ and every $i\le |w|$, after $i$ steps from the prefix emitter’s initial configuration on input $x$, the control state is $i$, the input head is at position $1$, and the output is the prefix of $w$ of length $i$.

**Proof.** Proceed by induction on $i$. At $i=0$, the initial configuration has state $0$, head position $1$, and empty output, as required. For the successor step, the induction hypothesis gives state $i$ and output $w.take\,i$. Since $i<|w|$, the machine’s emission transition writes $w_i$, leaves the input head in place, and advances to state $i+1$. The output therefore becomes $w.take(i+1)$, while the head remains at position $1$. The state, head position, and output determine the zero-work-tape configuration (`Cfg.ext_zero_tapes`); the run recurrence reduces the successor-time claim to this single transition (`MultiTapeTM.runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.Cfg.ext_zero_tapes`.
