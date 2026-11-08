<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.card_validComponentRootLabels_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Valid Component Root Labels

**Claim.** For any connected component, the number of root labels whose propagated labels satisfy every constraint in that component is at most $q$.

**Proof.** The valid root labels form a subset of the full label set, which is $	ext{Fin }q$. Hence their cardinality is at most the cardinality of that full set. The latter cardinality is $q$, giving the bound.
