<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinOracleTM.exists_plain_simulation_initCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Plain simulation of oracle computations

**Claim.** If a finite Turing machine decides the oracle language within the nondecreasing time bound $\tau$, then some finite ordinary Turing machine computes every output of the oracle machine's initialized run within $a(t+1)(t+1+\tau(t))$ steps for a constant $a$.

**Proof.** Apply the simulation theorem for monotone time bounds (\texttt{Turing.FinOracleTM.exists_plain_simulation_of_monotone}). It supplies a machine $P$ and constant $a$ that simulate a run started with the given tape contents when the query tape is blank. The initialized configuration has exactly this form: its work tapes are all blank, its heads are at the origin, and its output is empty. The equality identifying an initialized configuration with the configuration built from empty tape words is given by \texttt{Turing.Cfg.init_eq_ofWords}. Thus the simulation theorem yields a halting run of $P$ at some time $s\le a(t+1)(t+1+\tau(t))$ with the oracle machine's output. If this witness $s$ is shorter than the advertised computation time, extend $P$'s halted run to that time using the characterization of computation in time (\texttt{Turing.FinTM.computesInTime_iff}), the run decomposition \texttt{Turing.MultiTapeTM.runFrom_add}, and the fact that a halted configuration remains unchanged (\texttt{Turing.MultiTapeTM.runFrom_of_halt}). The output therefore remains the same at the advertised bound.

**Key facts.** `Turing.FinOracleTM.exists_plain_simulation_of_monotone`, `Turing.Cfg.init_eq_ofWords`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
