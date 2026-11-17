<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.expect_majorityThreeHardInput_skeleton_disagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disagreement on a three-coordinate hard input

**Claim.** Under the stated choices of the coordinate $i$ and sign-dependent coordinate map $j$, the expected indicator that the two constructed sign vectors differ is $2/3$.

**Proof.** Average the indicator over the finite product of the independent sign and coordinate choices. Record the two values $j(1)$ and $j(-1)$, then enumerate the possible choices of $i$, $j(1)$, and $j(-1)$. The condition that neither selected coordinate equals $i$ restricts the enumeration; evaluating the indicator in each remaining case and summing yields the stated average $2/3$.
