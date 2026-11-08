<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.BinarySubspaceSplit.liftFrequency_mem_perpendicularSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted frequency is perpendicular

**Claim.** Every lifted complementary frequency belongs to the perpendicular subspace of $H$.

**Proof.** By the characterization of the perpendicular subspace (FABL.mem_perpendicularSubspace_iff), it is enough to show that the lifted frequency has zero dot product with every $x\in H$. Regard such an $x$ as an element $h$ of $H$. The splitting isomorphism sends $(h,0)$ to $x$ by the specified compatibility of the split, so the inverse image of $x$ is $(h,0)$. The lifted frequency’s associated functional evaluates on this inverse image by taking the dot product of the complementary frequency with the second coordinate. That coordinate is zero, so the value is zero. This holds for every $x\in H$, proving perpendicularity.

**Key facts.** `FABL.mem_perpendicularSubspace_iff`.
