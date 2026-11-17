<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.splitCharacterSeed_card_le_three_cube_powers -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split seed cardinality bound

**Claim.** If the ambient cube is $\mathbb F_2^d$, then the number of split-character seeds is at most $2^{3d}$.

**Proof.** The complementary factor embeds injectively into the ambient cube: send $x$ to the point corresponding to $(0,x)$. If two such points agree, injectivity of the coordinate isomorphism implies $(0,x)=(0,y)$, and hence $x=y$. Therefore the complementary factor has at most $2^d$ elements. The subspace $H$ also has at most $2^d$ elements, since its inclusion into the ambient cube is injective. A seed consists of two complementary-factor elements and one element of $H$, so its cardinality is the product of their cardinalities and is at most $(2^d)^3=2^{3d}$.
