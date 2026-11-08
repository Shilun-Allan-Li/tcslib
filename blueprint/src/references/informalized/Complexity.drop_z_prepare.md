<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_z_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparing the outer word

**Claim.** Under the stated bounds, the machine reaches scan stage $1$ with pointer zero, end-marker register $2\,\mathrm{zlen}$, and the specified query, tail, and input-length values; all earlier configurations are safe and obey the register bound.

**Proof.** The initial registers are bounded by $4|h|+4$ using the register bound lemma (\texttt{dropValues\_bound}). The copy-run lemma (\texttt{drop\_copy\_run}) at stage $3$ copies the tail value into the end-marker register and advances to the decrement sequence. Two decrements of that register, justified by the decrement-run lemma (\texttt{drop\_decrement\_run}), change $2\,\mathrm{zlen}+2$ to $2\,\mathrm{zlen}$ and reach the pointer-clearing state. The bound $2\,\mathrm{zlen}+2\le |h|$ ensures the values remain within the register limit. One further step clears the pointer and enters scan stage $1$. Reachability transitivity joins these segments, and reflexivity accounts for the final unchanged configuration.

**Key facts.** `Complexity.dropValues_bound`, `Complexity.drop_copy_run`, `Complexity.drop_decrement_run`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.trans`.
