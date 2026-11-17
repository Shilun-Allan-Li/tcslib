<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_quad_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on encoded component lengths

**Claim.** Each of $|\alpha|$, $|x|$, $n$, and $t$ is at most the length of the nested encoding $\langle\alpha,\langle x,\langle1^n,1^t\rangle\rangle\rangle$.

**Proof.** The length of a pair encoding is twice the length of its first component, plus two separator bits, plus the length of its second component (`Turing.universal_pair_length`). Applying this formula successively to the three nested encodings, and using that the length of the word of $j$ ones is $j$, shows that the final length contains each of $|\alpha|$, $|x|$, $n$, and $t$ as a summand with nonnegative additional terms. Each is therefore bounded by the total length.

**Key facts.** `Turing.universal_pair_length`.
