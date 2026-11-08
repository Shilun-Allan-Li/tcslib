<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.DNFFormula.firstCompatibleTermIndex_eq_firstCompatibleTermIndexOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of First-Term Selections

**Claim.** For a nonconstant restricted function, the first compatible term index defined from nonconstancy agrees with the first compatible term index defined from the resulting nonempty set of compatible indices.

**Proof.** Both selections are the minimum of the same finite set of compatible term indices. The first definition uses the nonemptiness theorem applied to the bad restriction, while the second uses that very theorem's conclusion as its nonemptiness witness. Unfolding the two definitions therefore gives the same minimum.

**Key facts.** `FABL.DNFFormula.compatibleTermIndices_nonempty_of_badRestriction`.
