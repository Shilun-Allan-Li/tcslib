<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.Cfg.InWindow.core_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for an in-window configuration

**Claim.** If a configuration is in the window of radius $s$, then every work-tape head is within distance $s$ of the origin, and every nonblank tape cell is also within that distance.

**Proof.** Fix a work-tape index. The head bound is exactly the first part of the in-window hypothesis. For the cell bound, suppose a cell at position $z$ is nonblank. If its distance were not at most $s$, then its distance would be strictly greater than $s$. The second part of the in-window hypothesis would then make that cell blank, contradicting the supposition. Hence its distance is at most $s$.
