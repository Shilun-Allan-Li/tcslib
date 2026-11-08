<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.subprotocol_run_eq_of_reaches -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on Reaching Inputs

**Claim.** If a subprotocol $s$ of $p$ is reached by $(x,y)$, then running $p$ and $s$ on those inputs gives the same output.

**Proof.** Choose a subprotocol path from $s$ to $p$. By the definition of reaching a subprotocol, the hypotheses that $(x,y)$ reaches $s$ say exactly that $x$ and $y$ satisfy the respective path reachability conditions. The path agreement theorem then gives $p.run\ x\ y=s.run\ x\ y$ (\texttt{subprotocol\_run\_eq\_of\_reachesPath}).

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.subprotocol_run_eq_of_reachesPath`.
