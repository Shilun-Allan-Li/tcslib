<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersInner_duplicateAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duplicate-Coordinate Inner Product Formula

**Claim.** The Gowers inner product of the family obtained by replacing coordinate $i$ by $b$ is the average over $y$ of the square of the corresponding half expectation.

**Proof.** Apply the inner-product splitting identity (FABL.gowersInner_split_at) to the duplicated family. This expresses its inner product as the average over $y$ of the product of its two half expectations, for the fixed coordinate set respectively to $0$ and to $1$. For either bit $c$, the half expectation of the duplicated family equals the half expectation of the original family: in each factor of its defining product, the update setting coordinate $i$ to $b$ overrides the inserted value $c$. This equality holds for each spatial point and each remaining cube point, so it passes through the product and the average over spatial points. The two factors in the split are therefore equal to the same half expectation of the original family. Their product is its square, giving the claimed average.

**Key facts.** `FABL.gowersInner_split_at`.
