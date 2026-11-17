<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean :: Complexity.LogProg.inv_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant through a halting run

**Claim.** If a register-program simulation reaches an intermediate configuration without oracle-call states and with all register heads between $-1$ and $W$, and that configuration has a halting continuation with the stated output, head bounds, and invariant at earlier configurations, then the original configuration has the same halting outcome and bounds, with the invariant at every earlier configuration.

**Proof.** Choose a simulation duration $T_1$ from the initial configuration $c$ to $c'$, and a halting duration $T_2$ from $c'$ as supplied by the hypotheses. Run for $T_1+T_2$ steps. The run-addition identity ($\texttt{Complexity.LogProg.rrun\_add}$) identifies this endpoint with the continuation from $c'$, so it has the stipulated halting state, output, and head bounds.

For any time before the combined endpoint, split into two ranges. Before $T_1$, the simulation hypothesis says the configuration is a midpoint with no call state and bounded heads; the midpoint-to-invariant lemma ($\texttt{Complexity.LogProg.inv\_of\_mid}$) supplies the invariant. At or after $T_1$, write the time as $T_1+t'$. The run-addition identity identifies that configuration with the continuation at time $t'$, and $t'<T_2$, so the continuation hypothesis supplies the invariant there.

**Key facts.** `Complexity.LogProg.rrun_add`, `Complexity.LogProg.inv_of_mid`.
