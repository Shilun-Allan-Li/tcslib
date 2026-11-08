<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_u_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparing the inner word

**Claim.** Under the given size bounds, the machine reaches scan stage $2$ from copy stage $4$ with pointer zero, retained value $4\,\mathrm{ulen}+4$, inner value $4\,\mathrm{ulen}$, and the specified unchanged registers; all preceding configurations satisfy the safety condition and register bound.

**Proof.** First, the register bound lemma (\texttt{dropValues\_bound}) bounds every register in the initial configuration by $4|h|+4$. The copy-run lemma (\texttt{drop\_copy\_run}) at stage $4$ copies the pointer value into the retained register and advances to the next copy stage. Applying it again at stage $5$ copies the retained value into the inner register. The inner register is now $4\,\mathrm{ulen}+4$. The decrement-run lemma (\texttt{drop\_decrement\_run}) executes four decrements of that register, leaving $4\,\mathrm{ulen}$ and advancing to the pointer-clearing state. The hypotheses $2\,\mathrm{ulen}+2\le \mathrm{zlen}$ and $2\,\mathrm{zlen}+2\le |h|$ provide the inequalities needed for the register bounds throughout. One final machine step clears the pointer and enters scan stage $2$. Transitivity of reachability combines these segments, and reflexivity records the unchanged endpoint after that step.

**Key facts.** `Complexity.dropValues_bound`, `Complexity.drop_copy_run`, `Complexity.drop_decrement_run`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.trans`.
