<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.one_lt_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scale Exceeds One

**Claim.** The scale satisfies $1<S$.

**Proof.** Since $n>0$, multiplying $b$ by $n$ gives $b\le nb$. The hypothesis $2a\le b$ then yields $2a\le nb$. By the defining ceiling-division property of $S$, $nb\le aS$. Combining gives $2a\le aS$; cancelling the positive $a$ proves $2\le S$, and hence $1<S$.
