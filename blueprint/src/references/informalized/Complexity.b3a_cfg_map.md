<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_cfg_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Renaming the initial configuration state

**Claim.** Renaming the state of the initial $k$-tape configuration on input $x$, with $w$ stored on its first work tape, by $f$ gives the corresponding configuration with initial state $f(s)$.

**Proof.** The state component of the initial configuration is $s$, so applying the state map replaces it by $f(s)$. The input-head position, work-tape contents, work-tape head positions, and output are unchanged by state renaming. These are exactly the components of the initial configuration with state $f(s)$ and the same input and stored word.
