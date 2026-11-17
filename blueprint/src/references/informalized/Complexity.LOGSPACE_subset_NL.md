<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean :: Complexity.LOGSPACE_subset_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Log Space in Nondeterministic Log Space

**Claim.** Every language in $\mathsf{LOGSPACE}$ is in $\mathsf{NL}$: a finite Turing machine deciding it within a constant multiple of $\log_2(n)+1$ space has a nondeterministic machine with the same space bound.

**Proof.** By definition, $\mathsf{LOGSPACE}=\mathsf{SPACE}(\mathrm{logSpace})$ and $\mathsf{NL}=\mathsf{NSPACE}(\mathrm{logSpace})$. The general containment of deterministic space in nondeterministic space at each space bound therefore gives the inclusion.

**Key facts.** `Complexity.SPACE_subset_NSPACE`.
