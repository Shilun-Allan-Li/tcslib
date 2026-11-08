<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapParse_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Bit of a Parse Block

**Claim.** From the pair-reading state, when the input head is positioned at the first bit $b$ of the remaining word and the capture head is at displacement $0$, one step advances the input head by one, stores $b$ in the controller state, leaves the capture head at $0$, and appends $b$ to the output exactly when the emitting flag is true.

**Proof.** Unfold the machine's one-step transition. The state is the pair-reading state with no bit yet stored, and the input symbol at position $|\mathrm{pre}|+1$ is $b$: the configuration-reading fact `mapCfg_read` identifies this symbol with the corresponding entry of $x$, and $x=\mathrm{pre}\,b\,\mathrm{rest}$ makes that entry $b$. The pair parser's transition for a present bit moves the input head right, leaves the capture head fixed, stores $b$ as the first bit of the pair, and emits $b$ precisely when the flag $e$ is true. The action-application formula `mapAction_apply` gives the resulting configuration, while `moveInputPos_pos_of_ne_right` ensures that the right move increments this head position rather than clamping it at the right boundary. The resulting output is therefore $\mathrm{out}\mathbin{++}[b]$ if $e$ is true and $\mathrm{out}$ otherwise, which is $\mathrm{out}\mathbin{++}(\text{if }e\text{ then }[b]\text{ else }[])$.

**Key facts.** `Turing.FinTM.mapCfg_read`, `Turing.FinTM.mapAction_apply`, `Turing.moveInputPos_pos_of_ne_right`.
