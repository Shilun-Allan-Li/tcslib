<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy-Phase Run

**Claim.** For every $i\le |x|$, the wrapper reaches after $i$ steps the copy-phase configuration with input head at $i+1$, tape zero holding the length-$i$ prefix of $x$ with its head at $i$, all other tapes blank with heads at zero, and empty output.

**Proof.** Induct on $i$. At $i=0$, the initial configuration has the wrapper in phase $0$, input head at position $1$, blank work tapes with heads at zero, and empty output. These are exactly the fields of the stated copy-phase configuration with the empty prefix. For the successor case, the induction hypothesis identifies the configuration after $i$ steps. Since $i+1\le |x|$, we have $i<|x|$, so the one-step copy transition lemma says that this configuration advances to phase $0$ with input head at $i+2$, tape zero holding the prefix of length $i+1$ with head at $i+1$, and the other tapes and output unchanged (`a3_copy_step`). The run-length recursion says that the run for $i+1$ steps is one step applied to the run for $i$ steps (`runFrom_succ_eq_step'`). Combining these facts gives the required successor configuration; the remaining index arithmetic identifies its positions.

**Key facts.** `Complexity.a3_copy_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
