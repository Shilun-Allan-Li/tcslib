<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.init_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial cleaning-machine step

**Claim.** One step of the cleaning machine from its initial configuration with state $\mathrm{init}(q)$ yields the simulation configuration for $M$, started in state $q$ on $V$, at time zero.

**Proof.** At time zero, $M$ is still at its initial configuration ($\texttt{Turing.MultiTapeTM.runFrom\_zero}$). Thus the simulation configuration has state $\mathrm{sim}(q)$, input-head position $1$, blank data tapes, empty output, and on each marking tape only the origin mark specified by $\mathrm{markSet}(\varnothing)$. The cleaning machine's initialization transition changes its state to $\mathrm{sim}(q)$ and writes precisely those origin marks on the marking tapes; it leaves the data tapes blank, all head positions at zero, the input head in place, and the output empty. The input-head position is unchanged by a zero move ($\texttt{Turing.moveInputPos\_zero}$). Comparing these components gives the claimed equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
