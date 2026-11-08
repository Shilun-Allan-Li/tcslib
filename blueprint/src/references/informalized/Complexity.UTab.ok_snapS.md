<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ok_snapS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of Snapshot Sources

**Claim.** Under the stated lower bounds on registers $I$ and, when $t_0$ is false, $LB$, every source in the snapshot source list is valid for $\rho$.

**Proof.** Unfold the snapshot list and its membership condition. A source in the initial four entries is one of the two constants, one of the current-block sources, or the conditional previous-snapshot source. Constants are valid automatically; the current-block sources are valid by the bound on $I$. For the conditional source, split on $t_0$: when it is true the source is constant, and when it is false the hypothesis on $LB$ gives validity. A source in the middle concatenated list is one of the two end-of-cell sources, both of which are automatically valid. Every remaining source belongs to the previous-snapshot list, so the result follows from validity of all sources in that list (ok_psnS).

**Key facts.** `Complexity.UTab.ok_psnS`.
