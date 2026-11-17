<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.expect_vectorWalshCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a vector Walsh character

**Claim.** The uniform expectation of the vector Walsh character indexed by $\gamma$ is $1$ when $\gamma=0$, and $0$ otherwise.

**Proof.** If $\gamma=0$, the vector Walsh character is the trivial character, whose value is constantly $1$, so its expectation is $1$. Otherwise its character is nontrivial: if it were trivial, injectivity of the indexing map (`vectorWalshCharacter_injective`) and the fact that the zero index gives the trivial character (`vectorWalshCharacter_zero`) would force $\gamma=0$. The sum of a nontrivial additive character over a finite group is zero (`AddChar.sum_eq_ite`); dividing that sum by the size of the group gives expectation zero.

**Key facts.** `FABL.vectorWalshCharacter_injective`, `FABL.vectorWalshCharacter_zero`.
