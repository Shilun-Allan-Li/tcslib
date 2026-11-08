<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.sq_sq_sub_one_le_nine_mul_sq_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Deviation Bound

**Claim.** If $s^2=1$ and $(s-t)^2\le1$, then $(t^2-1)^2\le9(s-t)^2$.

**Proof.** Write $r=s-t$, so $t=s-r$. From $r^2\le1$ and $s^2=1$, one obtains $(r-2s)^2\le9$; for example, expanding and using $(r+s)^2\ge0$ gives this bound. Substituting $t=s-r$ and $s^2=1$ shows $(t^2-1)^2=r^2(r-2s)^2$. Since $r^2\ge0$, the bound on the second factor gives $(t^2-1)^2\le9r^2=9(s-t)^2$.
