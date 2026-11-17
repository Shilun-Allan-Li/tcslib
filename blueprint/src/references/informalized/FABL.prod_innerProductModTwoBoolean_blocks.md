<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.prod_innerProductModTwoBoolean_blocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block product of mod-two inner products

**Claim.** The product of the signs obtained from the rowwise mod-two inner products of $a$ and $c$ equals the sign obtained from their full mod-two inner product.

**Proof.** First express each block's Boolean function as the sign encoding of the dot product of its two row vectors, using the identity for block joining (`innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks`). The sign encoding of a sum in the two-element field is the product of the sign encodings of its summands (`signEncode_sum`), so the product over rows becomes the sign encoding of the sum of all rowwise coordinate products. Reindex this sum first by pairs of coordinates $(b,j)$ and then by the single coordinate indexing the length-$m^2$ arrays. These are exactly the terms in the full dot product of $a$ and $c$, giving the right-hand sign.

**Key facts.** `FABL.innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks`, `FABL.signEncode_sum`.
