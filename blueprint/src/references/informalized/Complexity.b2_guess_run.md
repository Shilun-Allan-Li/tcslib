<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_guess_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Guessing Phase

**Claim.** If the normalized scheduler remains active before every step in $w$, running the host on $w$ updates the scheduler configuration by $|w|$ steps and appends to $u$ exactly the choice bits at steps when the scheduler emits.

**Proof.** Proceed by induction on $w$, generalizing over the starting configuration $c$ and accumulated word $u$. For the empty word, the host has taken no steps, the emission mask and selected word are empty, and the claimed equality follows. For $w=b::w'$, liveness at time zero says that $c$ is active, so the one-step guessing rule applies (`b2_guess_step`): the host simulates one scheduler step and appends $b$ exactly when that step emits. The scheduler is still active at every time before the remaining run: at time $s$ of the run from the successor configuration, its state is the state at time $s+1$ of the original run, by the run-length shift identity (`runFrom_succ_eq_step`), and the original liveness hypothesis applies. Thus the induction hypothesis handles $w'$. The input list of choices for the remaining run is appended after the first step's contribution; associativity of list concatenation and the definitions of the emission mask and selection give exactly the stated accumulated word. The decomposition of the run into its first choice followed by the rest is `runWith_cons`.

**Key facts.** `Turing.NDTM.runWith_cons`, `Complexity.b2_guess_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
