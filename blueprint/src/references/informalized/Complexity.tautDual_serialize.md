<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization of the De Morgan Dual

**Claim.** For a CNF formula $\varphi$, scanning its binary serialization from the formula state, and flipping each bit read in a polarity state, produces the binary serialization of the DNF obtained by negating each literal of $\varphi$ in place.

**Proof.** Induct on the list of clauses. For the empty list, both serializations are the single terminating bit, and the scan leaves it unchanged. For a nonempty list $C::\varphi$, its serialization consists of the clause-start bit followed by the serialization of $C$ and then that of $\varphi$. The clause-scan lemma (`Complexity.tautDual_clause`) says that scanning this portion transforms the clause serialization into the serialization of the clause with each literal’s polarity negated, followed by the formula-state scan of the remaining suffix. The induction hypothesis identifies that remaining scan with the serialization of the dual of $\varphi$. Together these give exactly the serialization of the DNF whose terms are the polarity-negated clauses.

**Key facts.** `Complexity.tautDual_clause`.
