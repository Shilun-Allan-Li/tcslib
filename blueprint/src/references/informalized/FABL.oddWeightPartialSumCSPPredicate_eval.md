<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.oddWeightPartialSumCSPPredicate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partial Sum Predicate Evaluation

**Claim.** For every seed, input word, and proof word, evaluating the selected linear predicate on the variables assigned by those words returns true exactly when the partial sum check specified by that seed holds.

**Proof.** Split into the three kinds of seed. For the initial check, the scoped variables are the first two input bits and the first proof bit. The predicate accepts precisely when the sum of their corresponding elements of $\mathbb F_2$ is zero. The equivalence $a+b+c=0$ if and only if $c=a+b$ in $\mathbb F_2$ (\texttt{f₂\_add\_add\_eq\_zero\_iff\_eq\_add}) turns this into the stated initial partial sum check. For the final check, the scope consists of the last proof bit alone, and the predicate accepts exactly when that bit represents $1$, as required. For a step seed $k$, the scoped variables are the proof bits at $k$ and its successor and the input bit at position $k+2$. The predicate again tests that their sum is zero; the same field identity rewrites this as the required successor-proof-bit equation. In each case the Boolean decision procedures therefore have the same truth value.

**Key facts.** `FABL.f₂_add_add_eq_zero_iff_eq_add`.
