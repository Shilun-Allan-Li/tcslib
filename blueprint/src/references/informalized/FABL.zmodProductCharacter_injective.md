<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.zmodProductCharacter_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of product characters

**Claim.** For every positive modulus and natural number $n$, distinct index functions give distinct product characters.

**Proof.** Suppose two index functions $\alpha$ and $\beta$ define the same product character. Fix a coordinate $i$ and evaluate both characters on the vector that is $y$ at $i$ and zero elsewhere. The single-coordinate evaluation formula (`FABL.zmodProductCharacter_apply_single`) identifies these values with the cyclic characters indexed by $\alpha(i)$ and $\beta(i)$, respectively. They agree for every $y$, so the two cyclic characters are equal. Injectivity of the cyclic-character map (`FABL.zmodCharacter_injective`) gives $\alpha(i)=\beta(i)$. Since this holds at every coordinate, the index functions are equal.

**Key facts.** `FABL.zmodProductCharacter_apply_single`, `FABL.zmodCharacter_injective`.
