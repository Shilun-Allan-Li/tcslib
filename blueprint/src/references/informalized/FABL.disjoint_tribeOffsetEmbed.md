<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.disjoint_tribeOffsetEmbed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Coordinate Blocks

**Claim.** For distinct coordinates $i$ and $j$, the subsets formed by embedding their respective offsets from $T$ into the corresponding coordinate blocks are disjoint.

**Proof.** Suppose an element $x$ belongs to both embedded subsets. Then there are offsets $o_1$ and $o_2$ such that $x$ is the image of $(i,o_1)$ and also the image of $(j,o_2)$ under the product-to-index equivalence. Since that equivalence is injective, $(i,o_1)=(j,o_2)$. Equality of first components gives $i=j$, contrary to the hypothesis that they are distinct. Hence the embedded subsets are disjoint.
