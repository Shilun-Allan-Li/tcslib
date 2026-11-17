<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesBlockEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Coordinates of the Tribes Equivalence

**Claim.** The $i$th block of the image of $x$ under the block equivalence is the vector whose $j$th coordinate is the coordinate of $x$ indexed by $(i,j)$.

**Proof.** By definition, the block equivalence sends $x$ to the function whose value at block $i$ is `inputBlock x i`. Thus the asserted equality is the defining evaluation of the forward map.
