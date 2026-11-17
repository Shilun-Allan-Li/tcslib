<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.epsilon_sq_div_three_le_inv_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal Candidate Count Bound

**Claim.** If $C$ is a nonempty finite set, $\varepsilon>0$, and $|C|\le 3/\varepsilon^2$, then $\varepsilon^2/3\le 1/|C|$.

**Proof.** Nonemptiness gives $|C|>0$. Multiply the assumed bound $|C|\le 3/\varepsilon^2$ by the nonnegative number $\varepsilon^2$; since $\varepsilon>0$, this yields $|C|\varepsilon^2\le 3$. Dividing by the positive number $3|C|$ and rearranging gives $\varepsilon^2/3\le 1/|C|$.
