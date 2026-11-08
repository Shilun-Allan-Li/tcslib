<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.pr_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting During Print Simulation

**Claim.** Under the stated bounds and oracle behavior, if the output position plus the remaining printed register value exceeds $p$, the compiled simulation from the print-processing state eventually halts with answer true, while satisfying the prescribed bounds at all earlier steps.

**Proof.** Fix $d,j$ with $o_0+j+d=p$. The proof inducts on $d$, following the print loop. At each loop iteration the temporary register is $j$ and the output position is $o_0+j$; the original registers and pointer remain fixed. The invariant that all register values are at most $B$ holds initially and at each intermediate configuration, by the bound lemma for extended evaluations (`Complexity.CPSim.G_ev`).

If $d=0$, then $o_0+j=p$. The print-loop comparison finds that the temporary value $j$ equals the value of the register being printed, so the simulation proceeds to its output-position check. The payload comparison is true because the output position is $p$, by the characterization of binary-word equality with the input payload (`Complexity.CPSim.jeqIn_eq`). The machine enters the true-answer state and halts. The halting facts `Complexity.LogProg.AHalt.step` and `Complexity.LogProg.AHalt.ret` package these successive transitions and the invariant at all earlier configurations.

If $d>0$, then $j$ is strictly less than the printed register value. The print-loop comparison therefore continues the loop. The output-position check fails because $o_0+j<p$, again using `Complexity.CPSim.jeqIn_eq`. The machine increments the output position and temporary register, preserving the extended-assignment form by the update facts for those registers (`Complexity.CPSim.upd_rO` and `Complexity.CPSim.upd_rT`). The incremented values remain within $B$, so the invariant holds at the intermediate configurations. The induction hypothesis applies with $j+1$ and remaining distance $d-1$; its equation follows from $o_0+j+1=o_0+(j+1)$. This yields halting with true, and the step and return facts assemble the full bounded halting trace.

**Key facts.** `Complexity.CPSim.G_ev`, `Complexity.CPSim.ev_rO`, `Complexity.CPSim.jeqIn_eq`, `Complexity.CPSim.upd_rO`, `Complexity.CPSim.ev_rT`, `Complexity.CPSim.upd_rT`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.AHalt.ret`.
