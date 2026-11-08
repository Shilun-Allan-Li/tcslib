<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.detPart_step_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Choice Replacement

**Claim.** At a choice state of the nondeterministic program, the compiled deterministic machine halts in one step and appends the chosen answer bit to its previous output.

**Proof.** Since the choice map is defined at the current state, the specification of `nchoice` identifies the current configuration state as a program state at the start phase, say $(l,\mathrm{start})$, where the instruction at $l$ chooses between two successors. The deterministic replacement rule turns that choice instruction into the instruction that returns $\beta$ (`NARM.detPart_choose`). At this state there is no decider call, and the compiled transition is exactly the return action that emits $\beta$. Applying that action sets the successor state to the halting state and appends $\beta$ to the output word, proving both conclusions.

**Key facts.** `Complexity.LogProg.nchoice_spec`, `Complexity.LogProg.NARM.detPart_choose`.
