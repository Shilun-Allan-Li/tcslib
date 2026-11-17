<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordRun_trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Recorded Runs

**Claim.** Concatenating a recorded run from $a$ to $b$ in $t$ steps with one from $b$ to $c$ in $v$ steps gives a recorded run from $a$ to $c$ in $t+v$ steps, with the same avoidance and head-distance bounds.

**Proof.** The run-addition identity (\(\texttt{Turing.MultiTapeTM.runFrom_add}\)) says that the run from $a$ for $t+v$ steps is the run from its time-$t$ configuration for another $v$ steps. The first run ends at $b$, and the second ends at $c$, proving the endpoint condition. For avoidance at any time $u<t+v$, split into two cases. If $u<t$, the first recorded run gives avoidance. Otherwise write $u=t+(u-t)$; then $u-t<v$, so the second recorded run, started at $b$, gives avoidance at that time. For the head-distance bound at any $u\le t+v$, if $u\le t$ use the first run's bound. If $u>t$, write $u=t+(u-t)$ and apply the second run's bound, since $u-t\le v$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
