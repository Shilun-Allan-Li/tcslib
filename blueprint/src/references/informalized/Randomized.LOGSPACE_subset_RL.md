<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.LOGSPACE_subset_RL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Logspace in RL

**Claim.** Every language decidable deterministically in logarithmic space belongs to one-sided probabilistic logarithmic space, with acceptance probability at least $2/3$ on members and certain rejection on nonmembers.

**Proof.** Apply the general inclusion of deterministic space $s$ in one-sided randomized space $s$ (Randomized.SPACE_subset_RSPACE) to $s=\mathrm{logSpace}$. By definition, the resulting class is $\mathrm{RL}$, while the deterministic class is $\mathrm{LOGSPACE}$.

**Key facts.** `Randomized.SPACE_subset_RSPACE`.
