<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.BinarySubspaceSplit.character_restrictFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character from restricted frequency

**Claim.** If $\eta$ is perpendicular to $H$, then the character associated to its restricted frequency equals the sign encoding of the dot product of $\eta$ with each point $z$.

**Proof.** Fix $z$ and write its inverse image under the splitting isomorphism as $(h,a)$. Additivity of the isomorphism expresses $z$ as the sum of the images of $(h,0)$ and $(0,a)$. Since $\eta$ is perpendicular to $H$, its dot product with the first image vanishes: that image is $h$, which belongs to $H$. The dot product of $\eta$ with the second image equals the dot product of the restricted frequency with $a$ (the defining restriction identity). By additivity of the dot product, the latter is therefore the dot product of $\eta$ with $z$. Applying sign encoding gives the desired pointwise equality.

**Key facts.** `FABL.mem_perpendicularSubspace_iff`, `FABL.BinarySubspaceSplit.dotProduct_restrictFrequency`.
