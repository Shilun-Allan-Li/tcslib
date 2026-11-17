<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStop_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After a Clean Call

**Claim.** If the original machine first reaches its exit state at time $t>0$ with the specified result tape contents and output, then the call-stopping wrapper, started with its release flag down, reaches the corresponding halted configuration after $t+1$ steps.

**Proof.** Write $c$ for the original machine's initial configuration. The given time-$t$ configuration is live, since its state is the exit state rather than the halting state. The live-prefix fact ($\texttt{sat_live_prefix}$) therefore ensures that every configuration of the original run through time $t$ remains live. Induct on $v$ to show that, for every $v\le t$, the wrapper's configuration after $v$ steps is the original configuration at time $v$ with flag $0$ at time zero and flag $1$ thereafter. The zero-time case is the initial configuration. For the successor step, the previous configuration is live by the prefix fact, and if its flag is raised, the cleanliness hypothesis says its state is not the exit state. The wrapper-step lemma ($\texttt{satStop_step}$) then makes its next step exactly the original machine's step while raising the flag; the run recursion identifies this with the next configuration in the induction claim. At time $t$, positivity of $t$ makes the flag raised, and the endpoint hypothesis supplies the specified exit configuration and output. One further wrapper step detects the raised flag together with the exit state and takes the control action that halts without changing the tape contents or output. This gives the claimed configuration at time $t+1$.

**Key facts.** `Complexity.sat_live_prefix`, `Complexity.satStop_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
