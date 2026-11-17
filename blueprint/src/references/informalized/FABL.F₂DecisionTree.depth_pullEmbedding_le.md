<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.depth_pullEmbedding_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under pullback by an embedding

**Claim.** Under the stated correspondence between available coordinate sets, pulling a decision tree back along a coordinate embedding does not increase its depth.

**Proof.** Proceed by induction on the original tree, allowing the source coordinate set to vary. A leaf pulls back to a leaf, so its depth remains zero. At a query, consider whether its coordinate lies in the image of the embedding. If it does, the pullback retains a query, and the induction hypotheses bound the depth of each pulled-back child by the depth of its corresponding original child. Taking maxima and adding one gives the required depth bound. If the queried coordinate is not in the image, the pullback omits that query and follows only the zero-child in its recursive construction. The induction hypothesis bounds the resulting depth by the zero-child’s depth, which is at most the maximum of the two original child depths and hence at most the original tree’s depth.
