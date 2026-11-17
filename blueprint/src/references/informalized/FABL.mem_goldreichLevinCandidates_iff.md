<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.mem_goldreichLevinCandidates_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin candidate membership

**Claim.** A set $T$ belongs to the family formed by taking, for each $S$ in the active family, $S$ and $S\cup\{i\}$ exactly when some active set $S$ is either $T$ or satisfies $T=S\cup\{i\}$.

**Proof.** For each active set $S$, its children are exactly the two sets $S$ and $S\cup\{i\}$. The candidate family is the union of these children over all active sets. Thus $T$ belongs to the candidate family precisely when there is an active $S$ for which $T=S$ or $T=S\cup\{i\}$.
