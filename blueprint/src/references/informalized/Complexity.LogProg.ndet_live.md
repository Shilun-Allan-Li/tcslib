<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.ndet_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Compiled Live Step

**Claim.** If the deterministic interpretation takes one live step and the stated precondition and register bit-length bounds hold, then there is a time bound such that every choice word up to that length respects the register and decider head bounds, and every word of exactly that length reaches the initial configuration associated with the next label and register values, preserving input and output.

**Proof.** The simulation theorem for one register-program step (`arm_step`) gives a finite compiled deterministic run from the initial configuration to the configuration associated with $(l',v')$. At every earlier time, its invariant provides the register-head bounds and the decider-head bound. The endpoint has the required register bounds too, since its register tapes are positioned at zero in the associated initial configuration. The precondition supplies the call-simulation hypotheses needed by this theorem.

Let $M$ be this compiled deterministic machine. Whenever the compiled nondeterministic program offers a genuine choice, its deterministic part halts on the next step (`detPart_step_choose`). But the deterministic run under consideration is live at its endpoint. Hence no genuine choice state can occur before that endpoint (`avoid_of_live`). On all these states, the nondeterministic transition for either choice bit agrees with the transition of $M$ (`ncompileTM_tr`). The run-agreement theorem (`ndtm_runWith_eq_runFrom`) now identifies any choice-word run of length at most the deterministic time bound with the corresponding deterministic prefix. Therefore the deterministic invariant gives the required bounds for all such words, and words of exactly the bound reach the stated endpoint configuration.

**Key facts.** `Complexity.LogProg.arm_step`, `Complexity.LogProg.detPart_step_choose`, `Complexity.LogProg.avoid_of_live`, `Complexity.LogProg.ncompileTM_tr`, `Complexity.LogProg.ndtm_runWith_eq_runFrom`.
