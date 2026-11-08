<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.literalListHolds_of_tseitinClauseChain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of a Tseitin Clause Chain

**Claim.** If every clause in the Tseitin chain formed from a list of literals and a list of auxiliary literals contains a literal that holds, then the original list contains a literal that holds.

**Proof.** Proceed by recursion on the chain construction. If there are fewer than four original literals, or no auxiliary literal remains, the chain consists of the original list as a single clause, so the conclusion is exactly the hypothesis for that clause. In the recursive case, write the first four literals as $p,q,r,s$ and the first auxiliary literal as $u$. The first clause, $(p,q,u)$, is satisfied, and every clause in the recursively constructed tail beginning with $\neg u,r,s,\ldots$ is satisfied as well. By induction, that tail has a satisfied literal. If it is one of $r,s$, or a later original literal, the original list is satisfied. If it is $\neg u$, then $u$ holds by satisfaction of the first clause only if that clause's satisfied literal is $u$; but a literal and its negation cannot both hold, by the negation equivalence (`literalHolds_negate_iff_not`). Therefore the first clause must instead be satisfied by $p$ or $q$, either of which belongs to the original list. In all cases the original list contains a satisfied literal.

**Key facts.** `FABL.literalHolds_negate_iff_not`.
