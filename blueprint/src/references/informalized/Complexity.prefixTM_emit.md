<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.prefixTM_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix-emission phase

**Claim.** For binary strings $w,x$ and each $i\le |w|$, after $i$ steps of the prefixing machine on input $x$, it is in state $i$, its input head remains at position $1$, and its output is the prefix of $w$ of length $i$.

**Proof.** Proceed by induction on $i$. At zero steps the initial configuration has the initial state, head position $1$, and empty output, which is the length-zero prefix of $w$. For the successor step, the induction hypothesis places the machine in state $i$ with head still at position $1$ and output $w.take\ i$. The bound $i+1\le |w|$ ensures $i<|w|$, so the transition emits the $i$th bit of $w$ and advances to state $i+1$. It does not move the input head, leaving that head at position $1$. The output is the previous prefix with that next bit appended, hence $w.take\ (i+1)$. Since there are no work tapes, the state, input-head position, and output determine the configuration (`Cfg.ext_zero_tapes`); the run recurrence (`runFrom_succ_eq_step'`) identifies this transition with the next run configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.Cfg.ext_zero_tapes`.
