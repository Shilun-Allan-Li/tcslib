<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.proposition9_27_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Bribery Bound

**Claim.** For a monotone Boolean function whose mean is at least $-0.99$, the greedy bribery set raises the mean to at least $0.99$ and has size at most $10000n/\log n$.

**Proof.** Let $J$ be the set of coordinates selected by the greedy bribery process after $n$ steps. The process guarantees that bribing all coordinates in $J$ to $+1$ raises the mean to at least $0.99$ (`FABL.mean_briberySets_final_ge_target`). Its cumulative gain is at least the initial mean plus $|J|$ times the bribery increment (`FABL.mean_briberySets_ge_initial_add_card_mul`). The final mean is at most $1$, since the mean of any sign-valued function lies in $[-1,1]$ (`FABL.mean_toReal_mem_Icc`). These bounds, together with the stated expression for the increment in the proof, imply $|J|\,\frac{199\log n}{1000000n}\le 199/100$. Since $n\ge2$, $\log n>0$; rearranging gives $|J|\le10000n/\log n$.

**Key facts.** `FABL.mean_briberySets_final_ge_target`, `FABL.mean_briberySets_ge_initial_add_card_mul`, `FABL.mean_toReal_mem_Icc`.

**Caveat.** The proof source uses the definition of `briberyIncrement` in its arithmetic step, but that definition is not included among the supplied upstream facts.
