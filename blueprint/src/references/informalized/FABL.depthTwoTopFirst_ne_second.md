<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoTopFirst_ne_second -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First and second positions are distinct

**Claim.** For every ordering parameter in $\{0,1,2\}$, the first and second positions selected by its associated cyclic order are distinct.

**Proof.** There are three possible ordering parameters. Evaluating the cyclic choices in each case gives respectively $(0,1)$, $(1,2)$, and $(2,0)$ for the first and second positions. Each pair has unequal entries, so the positions are distinct in every case.
