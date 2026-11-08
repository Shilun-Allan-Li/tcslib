<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.abs_vectorWalshCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Magnitude of a Binary Walsh Character

**Claim.** For every $n$ and every $\gamma,x\in\mathbb F_2^n$, the absolute value of the Walsh character indexed by $\gamma$, evaluated at $x$, is $1$.

**Proof.** The Walsh character takes one of the two values $-1$ and $1$ (`vectorWalshCharacter_eq_neg_one_or_one`). In either case its absolute value is $1$.

**Key facts.** `FABL.vectorWalshCharacter_eq_neg_one_or_one`.
