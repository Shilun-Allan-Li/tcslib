<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.exists_rejecting_composed_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A rejecting clause in the composition

**Claim.** If the original verifier rejects at a fixed seed on the outer proof obtained by restricting the extended proof, then some clause index makes the composed verifier reject on the same input and extended proof.

**Proof.** Assume for contradiction that the composed verifier accepts for every clause index at the fixed seed. For each clause, acceptance of the three-query verifier is equivalent to that clause evaluating to $-1$ on the local assignment induced by the composed input and proof (`composeThreeQueryVerifier_accepts_iff`). This local assignment is exactly the extension formed from the original verifier's local bits and the auxiliary bits extracted from the extended proof (`compositionLocalAssignment_eq_extracted`). Every clause in the formula is indexed by some $q\in\{0,\ldots,K-1\}$, because the formula has exactly $K$ clauses. Consequently every clause evaluates to $-1$ on this single extended assignment. The characterization of a CNF evaluating to $-1$ as all its clauses evaluating to $-1$ (`FABL.CNFFormula.eval_eq_neg_one_iff`) shows that the formula is satisfied.

Soundness of the seedwise reduction now says that the original verifier accepts on those local bits and extracted auxiliaries. The local bits are the transcript bits for the original input and the restriction of the extended proof: their transcript agrees with the verifier's transcript on that outer proof (`localTranscript_outerLocalBits`). This contradicts the assumed rejection. Therefore at least one clause index is rejected by the composed verifier.

**Key facts.** `FABL.composeThreeQueryVerifier_accepts_iff`, `FABL.compositionLocalAssignment_eq_extracted`, `FABL.CNFFormula.eval_eq_neg_one_iff`, `FABL.localTranscript_outerLocalBits`.
