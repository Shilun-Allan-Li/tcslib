<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.RandReducible.of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Reductions Preserve Randomized Reducibility

**Claim.** If $B$ is polynomial-time many-one reducible to $C$, then $B$ is randomized-reducible to $C$.

**Proof.** Choose a polynomial-time reduction $f$ from $B$ to $C$, so that $y\in B$ exactly when $f(y)\in C$. On an encoded input $z$, use the deterministic output $f(\operatorname{fst}(z))$, where $\operatorname{fst}$ is the first-component decoding. This is polynomial-time: the reduction $f$ can be composed with the polynomial-time first-component map (`PolyTimeComputable.comp`, `polyTimeComputable_pairFstD`). For an input representing $x$, the reduction property makes the output-membership condition equivalent to $x\in B$ for every choice of random bits. Thus its success event is certain; formally its random-bit probability agrees with the probability of the always-true event (`randProb_congr`), which is $1$ (`randProb_true`). In particular it meets the required randomized-reduction probability bound.

**Key facts.** `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`, `Randomized.randProb_congr`, `Randomized.randProb_true`.
