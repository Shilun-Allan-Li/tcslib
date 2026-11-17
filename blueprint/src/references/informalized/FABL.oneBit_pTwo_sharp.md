<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.oneBit_pTwo_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp-noise one-bit inequality

**Claim.** For $1\le p\le2$, the $2$-norm of $a+\sqrt{p-1}\,b x$ on a uniform sign is at most the $p$-norm of $a+bx$.

**Proof.** Apply the one-bit $(p,2)$ inequality (\texttt{oneBit\_pTwo}) with noise parameter $\rho=\sqrt{p-1}$. This parameter is nonnegative because $p\ge1$, and it is at most itself, so both required noise hypotheses hold. The resulting inequality is exactly the claim.

**Key facts.** `FABL.oneBit_pTwo`.
