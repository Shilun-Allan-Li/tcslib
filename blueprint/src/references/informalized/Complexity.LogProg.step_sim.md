<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.step_sim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Step with Cleanup Tracks

**Claim.** When the cleaning machine is in simulation state $q'$ and its original tapes represent a configuration $c$ in state $q'$, one step performs the transition of $M$ on the original tapes and output. The additional tapes make the specified update at each old head position and move their heads with the corresponding original heads.

**Proof.** First, because $c$ is in state $q'$, its next configuration is obtained by applying the transition of $M$ from $q'$ to $c$. In the combined configuration, the input symbol and the symbols scanned on the original tapes are exactly those seen in $c$. Thus the cleaning machine in simulation state $q'$ applies that same transition: the original tapes, their head positions, input position, output, and simulated state become those of the next configuration of $M$. The definition of the cleaning state sends the machine into the next simulation state when that transition continues, and into the first cleanup phase when it halts; this is precisely the state recorded by `simSt` for the next configuration. On an additional tape, the head moves by the same amount as its corresponding original tape. At the old head position, if the additional tape already contains $1$, the transition leaves it unchanged; otherwise it writes $0$. All other cells are unchanged. The resulting additional-tape contents are therefore exactly the stated pointwise update, while their head positions match those of the original tapes after the simulated step.

**Key facts.** `Complexity.LogProg.ccfg_state`, `Complexity.LogProg.ccfg_work`, `Complexity.LogProg.ccfg_mark`.
