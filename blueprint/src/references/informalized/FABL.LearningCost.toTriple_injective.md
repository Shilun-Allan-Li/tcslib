<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningCost.toTriple_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Cost Triple

**Claim.** The map sending a learning cost to its triple of random-example calls, membership queries, and local computation steps is injective.

**Proof.** Take two learning costs whose triples agree. Equality of ordered triples gives equality of each corresponding component: their random-example counts, query counts, and work counts agree. Since a learning cost is determined by these three components, the two costs are equal.
