<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpTime.lean :: Complexity.NSPACE_subset_exp_dtime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Space Is in Exponential Time

**Claim.** If $S$ is space-constructible, then $\mathrm{NSPACE}(S)\subseteq\bigcup_{c\in\mathbb N}\mathrm{DTIME}(n\mapsto 2^{c(S(n)+1)})$.

**Proof.** Space-constructibility includes the lower bound $\logSpace(n)\le S(n)$ for every input length $n$. The general nondeterministic-space simulation theorem under precisely this lower-bound hypothesis (`NSPACE_subset_exp_dtime_of_le`) gives $\mathrm{NSPACE}(S)\subseteq\bigcup_{c\in\mathbb N}\mathrm{DTIME}(n\mapsto 2^{c(S(n)+1)})$. The constructibility machine and its positive space constant are not otherwise used in this proof.

**Key facts.** `Complexity.NSPACE_subset_exp_dtime_of_le`.
