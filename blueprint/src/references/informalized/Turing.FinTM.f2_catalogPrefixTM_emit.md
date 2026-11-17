<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPrefixTM_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitted catalog prefix

**Claim.** For Boolean words $w,x$ and every $i\le |w|$, after $i$ steps the catalog-prefix machine started on input $x$ is in state $i$, has input-head position $1$, and has output equal to the first $i$ symbols of $w$.

**Proof.** Induct on $i$. At zero steps, the initial configuration has state $0$, head position $1$, and empty output, which is the prefix of length zero. For the successor case, the bound implies $i<|w|$. By the induction hypothesis, the machine is in state $i$; its transition therefore emits $w_i$, leaves the input head at position $1$, and advances to state $i+1$. The resulting output is the prefix of $w$ of length $i+1$. The state, position, and output equalities determine the configuration by zero-tape extensionality (\texttt{Turing.Cfg.ext_zero_tapes}); the run recursion expresses the successor run as one step after the preceding run (\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step'}).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.Cfg.ext_zero_tapes`.
