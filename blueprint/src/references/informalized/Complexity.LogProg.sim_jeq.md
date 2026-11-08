<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_jeq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register equality simulation

**Claim.** The compiled program simulates the instruction testing whether registers $r$ and $s$ agree, reaches the corresponding successor label without changing the valuation or output, and keeps every intermediate work head in the interval $[-1,W]$ with no oracle call pending.

**Proof.** Apply the register-equality run lemma (`Complexity.LogProg.eq_run`) to the initial configuration, whose two register tapes contain the binary expansions of $v(r)$ and $v(s)$. It supplies a finite run to the equality-dependent successor and shows that every earlier configuration has no pending call and that the compared head position lies between $-1$ and the length of the binary expansion of $v(r)$. The compiled program's transition and call descriptions agree with those required by this run lemma because the instruction at $l$ is the given equality test. The initial and terminal configurations in that run are the corresponding equality-normalized configurations; the seam identity (`Complexity.LogProg.eqCfg_aseam`) identifies them with the stated configurations. At each intermediate time, the run lemma's configuration description leaves all other register heads at their initial position $0$, while the compared head is within the stated interval. Since the binary length is at most $W$, all head positions lie in $[-1,W]$, giving the required simulation.

**Key facts.** `Complexity.LogProg.eq_run`, `Complexity.LogProg.eqCfg_aseam`.
