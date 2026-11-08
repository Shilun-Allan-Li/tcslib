<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.uniformProbability_DNFTerm_eval_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability a DNF term is satisfied

**Claim.** For a conjunction of distinct-coordinate literals on a finite sign cube, the probability that the term evaluates to $-1$ under the uniform distribution is $2^{-\mathrm{width}(T)}$.

**Proof.** The number of cube points where the term evaluates to $-1$ is $2^{n-\mathrm{width}(T)}$ (\texttt{DNFTerm.card\_eval\_neg\_one}); each of its distinct literals fixes one coordinate, leaving the other coordinates free. The width is at most the dimension (\texttt{DNFTerm.width\_le\_dimension}). The sign cube has $2^n$ points, so the desired probability is the ratio $2^{n-\mathrm{width}(T)}/2^n=2^{-\mathrm{width}(T)}$, as asserted.

**Key facts.** `FABL.DNFTerm.card_eval_neg_one`, `FABL.DNFTerm.width_le_dimension`.
