<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.macroCfg_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from Head Positions

**Claim.** For any schedule-controller configuration $c$, reconstructing a macrostep configuration with $c$’s state and the actual positions of its unary-counter and guide heads returns $c$.

**Proof.** Configurations are equal once their state, input-head position, tape contents, work-head positions, and output agree. The first, second, third, and fifth components agree directly from the definition of the reconstruction. For the work-head positions, split an index among the first $k$ tapes and the last three tapes. The first group is preserved by construction. For the last three, the three possibilities are exactly head indices $0$, $1$, and $2$; `finThree_cases` supplies this exhaustive classification, and in each case the reconstructed position is the corresponding original position. Thus every component agrees.

**Key facts.** `Complexity.finThree_cases`.
