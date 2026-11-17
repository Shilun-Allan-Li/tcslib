<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHalt.lean :: Nat.Partrec.Code.not_computablePred_mem_haltingSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Undecidability of the Halting Set

**Claim.** The predicate that a natural number belongs to the halting set is not computable.

**Proof.** Assume membership in the halting set is computable. Then it has a computable characteristic function $f$, equal to true exactly on members of that set. From $f$, form the computable predicate on codes $c$ given by $f(\langle \operatorname{encode}(c),0\rangle)$; it remains computable because encoding and pairing are computable. By the definition of the halting set and the decoding of this pair, this predicate says exactly that the program coded by $c$ halts on input $0$. This contradicts the undecidability of the halting problem for programs run on input $0$ (`ComputablePred.halting_problem`). Therefore halting-set membership is not computable.
