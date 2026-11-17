<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.eval_parityBottomNextNodeInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Bottom Inputs Detect a Mismatch

**Claim.** The OR gate applied to the selected bottom-layer values is the exact OR-node value: it is $1$ when the block assignment agrees with the level-$1$ parity-tree assignment, and $-1$ otherwise.

**Proof.** 1. First characterize when the selected inputs contain a bottom-layer value equal to $-1$. If such an input exists, its membership in the selected set supplies a child position $j$ for which the child group is the one indexed by $(g,j)$ and the normalized block product differs from $a(j)$. The bottom-layer characterization says that this normalized block assignment equals the corresponding level-$0$ parity-tree assignment. Its product is therefore the level-$1$ parity-tree value at position $j$. If $a$ were the level-$1$ assignment, these values would agree at every position, contradicting the selected input's product mismatch.

2. Conversely, if $a$ differs from the level-$1$ assignment, there is some position $j$ where their values differ (the pointwise inequality principle, `FABL.exists_apply_ne_of_ne`). Choose the child group $(g,j)$ and take its block to be the actual level-$0$ parity-tree assignment there. This block is valid (`FABL.parityBlockValue_valid`), so normalization leaves it unchanged (`FABL.normalizeParityBlockAssignment_eq_self`). The resulting layer index belongs to the selected input set, since its block product is the level-$1 value at $j$, which differs from $a(j)$. Its bottom-layer value is $-1` by the bottom-layer characterization (`FABL.parityBottomLayerValues_eq_neg_one_iff`). Thus the selected inputs contain a $-1$ exactly when the assignments differ. The membership characterization used in both directions is `FABL.mem_parityBottomNextNodeInputs_iff`; the child-index identity is `FABL.parityChildGroup_val`, and the equality between a level-$0$ assignment and its block value is `FABL.parityTreeAssignment_zero_eq_blockValue`.

3. By definition, the OR gate returns $-1$ if and only if one of its selected values is $-1$; otherwise it returns $1$. The equivalence just proved therefore gives $-1$ exactly when the assignments differ, which is the exact OR-node value specified in the claim.

**Key facts.** `FABL.mem_parityBottomNextNodeInputs_iff`, `FABL.parityBottomLayerValues_eq_neg_one_iff`, `FABL.parityChildGroup_val`, `FABL.parityTreeAssignment_zero_eq_blockValue`, `FABL.exists_apply_ne_of_ne`, `FABL.parityBlockValue_valid`, `FABL.normalizeParityBlockAssignment_eq_self`.
