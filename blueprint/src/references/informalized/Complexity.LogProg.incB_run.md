<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.incB_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the increment carry phase

**Claim.** Under the given transition and non-call assumptions, the carry phase reaches state $\mathrm{next}$ with head at zero after $n+1$ steps; every earlier configuration remains in state $c_B$, on the same tape, with head between $-1$ and the initial position $p$.

**Proof.** Induct on $n$. When $n=0$, the relation $p+1=n$ forces $p=-1$. The head scans beyond the word, so the transition at $c_B$ sees no symbol; its prescribed carry action moves the head to zero and enters $\mathrm{next}$. The only earlier time is zero, when the state and head have the required form. For the successor step, the hypotheses imply that $p$ is a nonnegative position within $w$. The transition at $c_B$ therefore reads the symbol there and performs one carry-phase step, leaving the tape unchanged and moving the head to $p-1$. The remaining run is exactly the induction hypothesis applied at $p-1$ with the corresponding shorter countdown. The run-iteration addition law (`rrun_add`) composes this first step with the inductive run to give the endpoint after the required total number of steps. For an earlier time, either it is the initial time, or it is one step followed by an earlier time in the inductive run. In the latter case the induction bounds the head below by $-1$ and above by $p-1$, hence also by $p$, while retaining state $c_B$ and the same tape.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`, `Complexity.LogProg.regCfg_state`, `Complexity.LogProg.regCfg_read`, `Complexity.LogProg.apply_regAct`, `Complexity.LogProg.rrun_add`.
