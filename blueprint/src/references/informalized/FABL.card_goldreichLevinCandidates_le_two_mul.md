<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.card_goldreichLevinCandidates_le_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin candidate bound

**Claim.** The candidate family formed from each $S$ in an active family by including $S$ and $S\cup\{i\}$ has cardinality at most twice the size of the active family.

**Proof.** The candidate family is the union, over active sets $S$, of the two-element-or-smaller collection consisting of $S$ and $S\cup\{i\}$. The cardinality of a union is at most the sum of the cardinalities of its pieces, so it is at most the sum of $2$ over all active sets. That sum equals twice the cardinality of the active family.
