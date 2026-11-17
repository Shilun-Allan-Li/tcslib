<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinOracleTM.exists_plain_decider -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eliminating an oracle from a decider

**Claim.** If the oracle machine decides $L$ within $T(n)$ steps and a finite-state machine decides its oracle language $O$ within $\tau(n)$ steps, where $\tau$ is monotone, then a finite-state machine without an oracle decides $L$ within $a(T(n)+1)(T(n)+1+\tau(T(n)))$ steps for some natural number $a$.

**Proof.** First use the plain-simulation theorem for an initialized oracle computation (\texttt{Turing.FinOracleTM.exists_plain_simulation_initCfg}). It supplies a finite ordinary Turing machine $P$ and a constant $a$ such that any computation of the oracle machine on input $x$, with output $\mathrm{out}$ and time $t$, is reproduced by $P$ within $a(t+1)(t+1+\tau(t))$ steps. For each input $x$, take $t=T(|x|)$ and let $\mathrm{out}$ be the oracle machine's deciding output. Since it decides $L$, this output is the indicator of whether $x\in L$. The simulation therefore makes $P$ decide $L$, and its bound at this time is exactly the claimed one.

**Key facts.** `Turing.FinOracleTM.exists_plain_simulation_initCfg`.
