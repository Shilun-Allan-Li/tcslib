<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.card_eval_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of satisfying assignments

**Claim.** The number of sign assignments satisfying every literal of the term is $2^{n-\operatorname{width}(T)}$.

**Proof.** The satisfying assignments are in bijection with arbitrary sign assignments on the coordinates outside the term's support (`T.satisfyingEquiv`). Thus their number is the number of functions from the outside coordinates to the two possible signs. The outside set has cardinality $n-|\operatorname{support}(T)|$, so this count is $2^{n-|\operatorname{support}(T)|}$. The support-size identity $|\operatorname{support}(T)|=\operatorname{width}(T)$ (`FABL.DNFTerm.card_support`) yields the stated count. The proof identifies the satisfying subtype's cardinality with the filtered finite-set count and uses the usual cardinality formula for functions into a two-element set.

**Key facts.** `FABL.DNFTerm.card_support`.
