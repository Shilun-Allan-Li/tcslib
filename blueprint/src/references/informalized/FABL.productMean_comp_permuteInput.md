<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productMean_comp_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation Invariance of Product Means

**Claim.** Permuting the coordinates of an input does not change the product mean of a function on the product space.

**Proof.** Expand the product mean as a finite sum over all inputs. Reindex this sum by the bijection that sends each input to the input with permuted coordinates. Under this reindexing, the function is evaluated at the permuted input on both sides. The product probability of an input is unchanged by permuting its coordinates (`productProbabilityPMF_permuteInput`), so corresponding summands agree and hence the means are equal.

**Key facts.** `FABL.productProbabilityPMF_permuteInput`.
