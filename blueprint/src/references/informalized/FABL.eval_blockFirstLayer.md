<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.eval_blockFirstLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-layer gate characterization

**Claim.** The indexed first-layer AND gate outputs $-1$ exactly when its assigned sign pattern agrees at every position with the restriction of $x$ to the coordinates selected for its block.

**Proof.** The first-layer gate is an AND term, so its output is the evaluation of the corresponding block minterm. The layer's indexing bijection selects the block and assignment encoded by $i$; its length lemma justifies the index cast. The block-minterm characterization says this term outputs $-1$ exactly when its assignment equals the selected restriction of $x$ (`FABL.blockMinterm_eval_eq_neg_one_iff`). Equality of these functions is precisely agreement at every position.

**Key facts.** `FABL.length_blockFirstLayer`, `FABL.blockMinterm_eval_eq_neg_one_iff`.
