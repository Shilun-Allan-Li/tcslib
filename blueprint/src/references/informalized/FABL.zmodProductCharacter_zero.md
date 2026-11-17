<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.zmodProductCharacter_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product character at zero

**Claim.** The product character indexed by the zero function is the trivial character on $(\mathbb Z/m\mathbb Z)^n$.

**Proof.** Evaluate both characters at an arbitrary vector. Each factor in the product is the cyclic character indexed by zero. The standard residue-to-character equivalence sends zero to the zero additive character, whose value at every input is one. Thus every factor is one, so the product is one, which is the value of the trivial character.
