<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.zmodProductCharacter_apply_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product character on a single coordinate

**Claim.** Evaluating the product character indexed by $\alpha$ on the vector supported at coordinate $i$ with value $y$ gives the cyclic character indexed by $\alpha(i)$ evaluated at $y$.

**Proof.** By the product-character evaluation formula (`FABL.zmodProductCharacter_apply`), the value is the product over coordinates $j$ of the cyclic character indexed by $\alpha(j)$ evaluated at the corresponding coordinate of the input. For the vector supported at $i$, that coordinate is $y$ when $j=i$ and zero otherwise. A character takes zero to one, so every factor except the $i$th is one. The product therefore reduces to the $i$th factor, as claimed.

**Key facts.** `FABL.zmodProductCharacter_apply`.
