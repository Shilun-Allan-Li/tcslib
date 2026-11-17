<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.BPdot_P_eq_BPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized reductions to polynomial time

**Claim.** The class of languages that reduce by a many-one reduction to some language in P equals the class decidable by polynomial-time randomized verifiers with success probability at least $2/3$ on members and nonmembers.

**Proof.** First, if a language reduces to a language in P, that P language has a bounded-error randomized verifier; composing the reduction with this verifier gives a BPP verifier for the original language (\texttt{Randomized.inBPP_polyTimeModel_of_mem_P} and \texttt{Randomized.InBPP.of_randReducible}). Conversely, take a BPP verifier $M$ and its polynomial-time languages $V_1,V_0$ witnessing efficiency. Use the identity reduction to $V_1$, which is in P, and use $M$ itself as the randomized procedure. The verifier's acceptance probability on members transfers to membership in $V_1$ because $M(x,r)$ agrees with membership of the encoded pair in $V_1$. On nonmembers, the verifier's probability of outputting false transfers to rejection by $V_1$. In each case, enlarging the set of random strings on which the corresponding event holds cannot decrease its probability (\texttt{Randomized.randProb_mono}). The identity is polynomial-time computable (\texttt{Complexity.polyTimeComputable_id}), so this witnesses the required reduction representation.

**Key facts.** `Randomized.InBPP.of_randReducible`, `Randomized.inBPP_polyTimeModel_of_mem_P`, `Complexity.polyTimeComputable_id`, `Randomized.randProb_mono`.
