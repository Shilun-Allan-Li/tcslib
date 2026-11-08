<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_guess_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Guessing Phase

**Claim.** Running the guessing-phase machine from the invariant configuration for $(d,u)$ under choice word $w$ gives the invariant configuration for the machine configuration reached after $|w|$ steps, with selected choice bits appended to $u$ at the emission steps.

**Proof.** Induct on $w$, with the starting configuration and captured word allowed to vary. For the empty word, the run takes no steps; the selected word is empty, so the invariant configuration is unchanged. For $w=b::w'$, first apply the one-step correspondence: choice bit $b$ advances the simulated machine by one step and appends $b$ to the captured word exactly when that step emits an output symbol (`cont_guess_step`). Then apply the induction hypothesis to the remaining choices $w'$. The emission mask for the whole word consists of the first step’s emission indicator followed by the mask for the remaining run; selection therefore consists of the possible initial bit followed by the remaining selected bits. Concatenation gives the stated accumulated captured word, and the run-length identity identifies the simulated configuration with the one reached after $|w|$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.NDTM.runWith_cons`).

**Key facts.** `Complexity.cont_guess_step`, `Turing.NDTM.runWith_cons`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
