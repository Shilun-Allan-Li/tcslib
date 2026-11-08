<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.exists_signValue_mul_eq_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A sign realizing absolute value

**Claim.** For every real number $c$, one of the signs $\sigma\in\{-1,1\}$ satisfies $\sigma c=|c|$.

**Proof.** If $c\geq0$, choose $\sigma=1$; then $\sigma c=c=|c|$. If $c<0$, choose $\sigma=-1$. The sign has real value $-1$ (`FABL.signValue_neg_one`), so its product with $c$ is $-c=|c|$.

**Key facts.** `FABL.signValue_neg_one`.
