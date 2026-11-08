<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_run_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Wrapper follows the first return

**Claim.** If the original run avoids the exit state at every intermediate time and reaches the specified canonical exit configuration at time $t>0$, then the wrapper started in phase $2$ reaches its state-renamed version at exactly time $t$.

**Proof.** Let $c$ be the canonical entry configuration. The wrapper’s transition from phase $2$ is exactly the original machine’s transition from the entry state, with the successor state renamed into the right-hand summand. Thus its first step agrees with the original run’s first step after renaming. The first-return hypothesis implies that, in the original run starting from this first-step configuration, the exit state is avoided for the next $t-1$ steps: a visit at time $j<t-1$ there would be a visit at time $j+1$ in the original run, strictly between $0$ and $t$. Apply the guarded-run lemma (Complexity.a3_run_guarded) to these remaining steps. The original run from the first-step configuration reaches the prescribed exit configuration after $t-1$ steps, since a run of $t$ steps is one step followed by a run of $t-1$ steps (Turing.MultiTapeTM.runFrom_succ_eq_step). Combining the initial step with this remaining run gives the claimed wrapper configuration at time $t$.

**Key facts.** `Complexity.a3_run_guarded`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
