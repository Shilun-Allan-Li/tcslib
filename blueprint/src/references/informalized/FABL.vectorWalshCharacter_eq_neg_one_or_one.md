<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorWalshCharacter_eq_neg_one_or_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of Binary Walsh Characters

**Claim.** For $\gamma,x\in\mathbb{F}_2^n$, the Walsh character indexed by $\gamma$, evaluated at $x$, is either $-1$ or $1$.

**Proof.** The Walsh character value is the binary sign of the dot product (`FABL.vectorWalshCharacter_apply`). In $\mathbb{F}_2$, the dot product is either $0$ or $1$: if it is zero, the binary sign is $1$; if it is nonzero, it must be $1$, and the binary sign is $-1$. Thus the character value is one of the two stated real numbers.

**Key facts.** `FABL.vectorWalshCharacter_apply`.
