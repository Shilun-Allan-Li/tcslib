<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignPredicate.randomizedValue_negateInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negating Inputs in Randomized Evaluation

**Claim.** The randomized value of the predicate with selected inputs negated at means $\mu$ equals the randomized value of the original predicate at the correspondingly negated mean vector.

**Proof.** Convert both randomized values to multilinear extensions using the identity between randomized evaluation and the multilinear extension (\texttt{FABL.SignPredicate.randomizedValue_eq_multilinearExtension}). The selected coordinate negations preserve the interval $[-1,1]$, so this identity applies to both vectors of means. The multilinear-extension input-negation identity (\texttt{FABL.SignPredicate.multilinearExtension_negateInputs}) then identifies the two expressions.

**Key facts.** `FABL.SignPredicate.randomizedValue_eq_multilinearExtension`, `FABL.SignPredicate.multilinearExtension_negateInputs`.
