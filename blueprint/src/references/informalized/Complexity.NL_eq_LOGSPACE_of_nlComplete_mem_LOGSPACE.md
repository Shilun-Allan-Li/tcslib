<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean :: Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A log-space complete language collapses the classes

**Claim.** If $C$ is NL-complete and belongs to LOGSPACE, then $\mathrm{NL}=\mathrm{LOGSPACE}$.

**Proof.** For the inclusion from NL to LOGSPACE, take any language $B$ in NL. Completeness gives a log-space reduction from $B$ to $C$, and log-space reducibility transfers membership in LOGSPACE from $C$ to $B$ (Complexity.mem_LOGSPACE_of_logspaceReducible). Hence every NL language lies in LOGSPACE. For the reverse inclusion, use the general containment LOGSPACE $\subseteq$ NL (Complexity.LOGSPACE_subset_NL). The two inclusions establish equality.

**Key facts.** `Complexity.mem_LOGSPACE_of_logspaceReducible`, `Complexity.LOGSPACE_subset_NL`.
