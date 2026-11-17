<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_subtype_eq_countP_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting True Predicate Instances

**Claim.** For a decidable predicate $p$ on $\mathrm{Fin}(q)$, the number of indices satisfying $p$ equals the number of true instances of $p$ in the list $0,1,\ldots,q-1$.

**Proof.** The cardinality of the subtype of indices satisfying $p$ is the sum over $i\in\mathrm{Fin}(q)$ of $1$ when $p(i)$ holds and $0$ otherwise. The finite-sum identity identifying this sum with the count of true instances in the list generated from all indices gives the desired equality (`sum_ite_eq_countP_ofFn`).

**Key facts.** `FABL.sum_ite_eq_countP_ofFn`.
