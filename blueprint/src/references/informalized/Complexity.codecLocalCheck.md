<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecLocalCheck -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF representation of a local Boolean function

**Claim.** For an inhabited variable type, any Boolean function of $m$ Boolean inputs can be represented after wiring by a CNF of cost at most $2^m(m+1)$, with evaluation agreeing for every assignment.

**Proof.** Use the standard truth-table CNF representation (`Complexity.exists_cnf_boolFun`) of the Boolean function on the $m$ indexed inputs. It has at most $2^m$ clauses, each of width at most $m$, and evaluates to the given function. Relabel its natural-number variables by sending each index below $m$ to the corresponding wired variable, and all other indices to a default element of the inhabited type. Relabeling preserves CNF cost (`Complexity.codecCnfCost_relabel`). Each clause contributes its length plus one to the cost, so its cost is at most $m+1$; summing over at most $2^m$ clauses gives the required bound, using the flat-map cost estimate (`Complexity.codecCnfCost_flatMap_le`). The relabelled formula's evaluation is the original truth-table evaluation with each input replaced by the value assigned to its wired variable, as required.

**Key facts.** `Complexity.exists_cnf_boolFun`, `Complexity.codecCnfCost_relabel`, `Complexity.codecCnfCost_flatMap_le`.
