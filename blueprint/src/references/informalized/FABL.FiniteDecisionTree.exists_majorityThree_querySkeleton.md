<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.FiniteDecisionTree.exists_majorityThree_querySkeleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Query Structure for Majority Trees

**Claim.** A tree computing majority on three signs must query a coordinate at its root, then a different coordinate after either root answer, and then the remaining coordinate whenever that second answer differs from the first.

**Proof.** A leaf cannot compute majority: the all-positive input has output $1$, while the all-negative input has output $-1$, so a constant leaf label cannot be correct on both. Thus the tree has a root query, say at $i$. Fix its answer $a$. If the corresponding child were a leaf, consider the two inputs agreeing with value $a$ at $i$ and having the same fixed value at one other coordinate, but opposite values at the third. The root follows the same branch on both inputs, while majority takes opposite values; hence that child cannot be a leaf. It must query some $j$, and availability after the root query forces $j\ne i$. Now fix a second answer $b\ne a$. If the resulting child were a leaf, choose inputs with values $a,b$ at $i,j$ and opposite signs at the remaining coordinate. The two fixed-coordinate majority identities show that these inputs have opposite majority outputs, contradicting a constant leaf. Therefore this child also queries a coordinate $k$, which must be available after erasing both $i$ and $j$, so it is distinct from each. The identities used here are that fixing one coordinate to $a$ and the other two equal to $s$ forces majority to be $s$ (`majority_majorityThreeFixedOneInput`), and fixing two distinct coordinates to opposite signs while the remaining coordinate is $s$ likewise forces majority to be $s$ (`majority_majorityThreeFixedTwoInput`).

**Key facts.** `FABL.majority_majorityThreeFixedOneInput`, `FABL.majority_majorityThreeFixedTwoInput`.
