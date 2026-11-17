<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.eval_parityNextLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Next Parity Layer Evaluation

**Claim.** For a gate and actual block assignment, applying the dual gate to the specified next-layer inputs yields the level-$q$ value at the chosen index, with the dual gate and the assignment formed from the products of the actual child blocks.

**Proof.** Use the layer-indexing identity to identify the selected list entry with the next-node input set for the group and block assignment corresponding to the chosen index (`FABL.get_parityNextLayer`). The node-input evaluation theorem says that applying the dual gate to this set yields the exact node value determined by whether that block assignment matches the assignment assembled from the products of the actual child blocks (`FABL.eval_parityNextNodeInputs`). By definition, that exact node value is precisely the level-$q$ layer value at the chosen index for the dual gate and the assembled assignment. The list length formula (`FABL.length_parityNextLayer`) accounts for the index cast used to select the list entry.

**Key facts.** `FABL.get_parityNextLayer`, `FABL.eval_parityNextNodeInputs`, `FABL.length_parityNextLayer`.
