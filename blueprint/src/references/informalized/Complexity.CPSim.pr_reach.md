<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.pr_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Through a Print Simulation

**Claim.** Under the stated bounds and oracle behavior, if $o_0+\rho(r)\le p$, then the compiled machine reaches the simulation state following the print instruction, with the output position and temporary register both equal to $\rho(r)$ added to their respective starting values, while satisfying the prescribed bounds at every earlier step.

**Proof.** Induct on $d$, where $j+d=\rho(r)$. The proof follows the print loop from temporary value $j$ and output position $o_0+j$. At every configuration, the state and register bounds hold by the extended-evaluation bound lemma (`Complexity.CPSim.G_ev`).

When $d=0$, we have $j=\rho(r)$. The print-loop comparison detects equality between the temporary value and the register being printed, and the machine transitions directly to the simulation state following the print instruction. The resulting configuration has output position $o_0+\rho(r)$ and temporary value $\rho(r)$; zero further steps are needed (`Complexity.LogProg.AReach.refl`).

When $d>0$, $j<\rho(r)$, so the print-loop comparison continues the loop. Since $o_0+j<\rho(r)+o_0\le p$, the output-position comparison does not yet match the input payload, by the binary-word characterization (`Complexity.CPSim.jeqIn_eq`). The machine increments both the output position and temporary register, and the update facts (`Complexity.CPSim.upd_rO` and `Complexity.CPSim.upd_rT`) show that the resulting assignment has the same extended form with values $o_0+(j+1)$ and $j+1$. The bounds persist at this intermediate step. The induction hypothesis applies to $j+1$ and $d-1$, since $(j+1)+(d-1)=\rho(r)$, and reaches the target configuration. Repeatedly adjoining the current bounded step (`Complexity.LogProg.AReach.step`) gives the required reachability.

**Key facts.** `Complexity.CPSim.G_ev`, `Complexity.CPSim.ev_rO`, `Complexity.CPSim.jeqIn_eq`, `Complexity.CPSim.upd_rO`, `Complexity.CPSim.ev_rT`, `Complexity.CPSim.upd_rT`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.step`.
