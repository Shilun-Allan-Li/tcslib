<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.sim_step_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Live-step simulation by the cleaning machine

**Claim.** If the original machine is live after $t$ steps, one step of the cleaning machine from the encoded configuration at time $t$ equals the encoded configuration at time $t+1$.

**Proof.** Since the original configuration at time $t$ is live, write its state as some $q'$. The encoding's state is therefore the cleaning machine's simulation state for $q'$, while its input position, original work tapes and heads, marks, and output are those of the original configuration. Apply the simulation-step identity (`step_sim`): it advances the simulated machine by one transition and updates the cleaning-machine tracks by marking the relevant visited position. The original run at time $t+1$ is that one-step successor (`runFrom_succ_eq_step'`). Its visited-position set is the previous set with the time-$t$ head position inserted (`visB_succ`), and the mark tape represents precisely this insertion (`wr_markSet`). Substituting these updates into the encoded configuration gives the claimed equality.

**Key facts.** `Complexity.LogProg.step_sim`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.LogProg.visB_succ`, `Complexity.LogProg.wr_markSet`.
