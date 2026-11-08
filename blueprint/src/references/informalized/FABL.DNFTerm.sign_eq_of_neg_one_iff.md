<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DNFTerm.sign_eq_of_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signs determined by the negative-sign test

**Claim.** If two signs in $\{-1,1\}$ are each negative exactly in the same circumstances, then they are equal.

**Proof.** Each sign is either $1$ or $-1$. If the first is $-1$, the assumed equivalence forces the second to be $-1$ as well. If the first is $1$, the equivalence rules out the second being $-1$, so it must be $1$. In either case the signs agree.
