<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.sScan_sel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selection of a Paired Scan Component

**Claim.** For either Boolean $b$, the corresponding component of the paired scan is the fold of the update rule $G(b)$ over the paired decoded blocks, starting from the initial scan state.

**Proof.** The blockwise decomposition theorem `sScan_eq` expresses the paired scan as the ordered pair of folds, first for $G(\mathrm{false})$ and then for $G(\mathrm{true})$. If $b$ is false, selecting the first component gives the fold for $G(b)$; if $b$ is true, selecting the second gives that fold. These two cases establish the result.

**Key facts.** `Complexity.Codec.sScan_eq`.
