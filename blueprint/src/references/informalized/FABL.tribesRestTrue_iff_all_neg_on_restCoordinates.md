<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tribesRestTrue_iff_all_neg_on_restCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rest Coordinates Characterize the Block Condition

**Claim.** Let $w,s$ be natural numbers, let $i$ be a coordinate in the sign cube of dimension $sw$, and let $x$ be an element of that cube. Every coordinate in the block containing $i$, except the coordinate corresponding to $i$, has sign $-1$ if and only if every coordinate in the block's rest-coordinate set has sign $-1$.

**Proof.** Write $i$ as the pair consisting of its block index and its position within that block. In the forward direction, take any coordinate in the rest-coordinate set. Membership means it is the image of some position $o$ in the same block, and that it is not $i$. The identity saying that the coordinate-pair equivalence sends the pair for $i$ back to $i$ (`finProdFinEquiv_tribesCoord`) shows that $o$ differs from the position of $i$. The block condition therefore forces the sign at this coordinate to be $-1$. Conversely, take any other position $o$ in the block of $i$. Its corresponding ambient coordinate belongs to the block-coordinate set (`mem_tribesBlockCoordinates`). It is not $i$: otherwise injectivity of the coordinate-pair equivalence would force $o$ to equal the position of $i$. Thus it belongs to the rest-coordinate set, and the assumed sign condition gives sign $-1$.

**Key facts.** `FABL.finProdFinEquiv_tribesCoord`, `FABL.mem_tribesBlockCoordinates`.
