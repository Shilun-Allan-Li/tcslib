<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.zmodProductCharacter_bijective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product-character parametrization

**Claim.** For every positive modulus and natural number $n$, the map sending an index function to its product character is bijective.

**Proof.** For a map between these finite types, bijectivity follows from injectivity together with equality of the cardinalities of the domain and codomain. Injectivity is supplied by `FABL.zmodProductCharacter_injective`. The cardinalities agree because the number of characters of a finite abelian group equals the order of the group (`AddChar.card_eq`). Hence the product-character map is bijective.

**Key facts.** `FABL.zmodProductCharacter_injective`.
