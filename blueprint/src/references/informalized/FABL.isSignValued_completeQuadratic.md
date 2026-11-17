<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isSignValued_completeQuadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Quadratic Is Sign-Valued

**Claim.** The complete quadratic function takes values of absolute value $1$ at every Boolean-cube input.

**Proof.** Fix an input. The complete quadratic function is the binary sign of its complete quadratic bit (\(\texttt{completeQuadratic\_apply}\)). That bit lies in $\mathbb F_2$, whose only elements are $0$ and $1$. If it is $0$, the binary sign is $1$, so its absolute value is $1$. Otherwise it is $1$, and the binary sign is $-1$, again of absolute value $1$.

**Key facts.** `FABL.completeQuadratic_apply`.
