<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.expect_nandParity_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaged NAND Parity Identity

**Claim.** If $P$ has uniform mean zero on a finite type $A$, then the uniform average over pairs of the stated NAND parity expression multiplied by $P(a)P(b)$ equals one half the square of the uniform average of $F(a)P(a)$.

**Proof.** Rewrite the pairwise numerator, after multiplication by $P(a)P(b)$ and division by $2$, as the sum of four separated products:
\[
-\frac{P(a)}2P(b)-\frac{F(a)P(a)}2P(b)-P(a)\frac{F(b)P(b)}2+\frac{F(a)P(a)}2F(b)P(b).
\]
The expectation of each product factors into the product of its one-variable expectations (\texttt{FABL.expect\_pair\_mul\_separate}). The first three terms vanish because one factor has mean $\mathbb E P=0$. The last term is $\frac12(\mathbb E_a F(a)P(a))^2$, using linearity to take the constant factor $1/2$ outside the expectation. This is the desired identity.

**Key facts.** `FABL.expect_pair_mul_separate`, `FABL.expect_div_const`.
