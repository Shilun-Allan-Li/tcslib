<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.E3LinSignTester.toE3SatTester_usesMaxE3Sat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Converted Tester Uses Three-Literal Clauses

**Claim.** Every predicate used by the converted E3-Sat tester is a three-literal clause that accepts exactly when at least one queried sign differs from its corresponding falsifying sign.

**Proof.** To show that every predicate of the converted tester belongs to the set of three-literal clauses, take an arbitrary seed and clause. The converted check's predicate is, by its definition, the E3-Sat clause whose falsifying signs are determined by the seed's right-hand-side sign and that clause. This exhibits the predicate as a member of the stated set, and the definition of that clause gives its three-literal acceptance condition.
