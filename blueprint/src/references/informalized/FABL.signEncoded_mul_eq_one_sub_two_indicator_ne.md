<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.signEncoded_mul_eq_one_sub_two_indicator_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Product and Agreement

**Claim.** For $a,b\in\mathbb{F}_2$, the product of their real sign values is $1$ when they agree and $-1$ when they differ; equivalently, it is $1-2$ times the indicator of disagreement.

**Proof.** First observe that $a+b=0$ in $\mathbb{F}_2$ exactly when $a=b$: if the sum is zero, then $a=-b=b$ because negation is the identity in $\mathbb{F}_2$; conversely, equal summands add to zero. Apply the identity relating the indicator of $a+b=c$ to the product of the three sign values (\texttt{FABL.two_mul_blrIndicator_sub_one}) with $c=0$. Using the equivalence just established, this expresses the product of the sign values of $a$ and $b$ in terms of the indicator that they agree. Finally, split into the cases $a=b$ and $a\ne b$: the agreement case gives product $1$ and the disagreement case gives product $-1$, precisely the claimed indicator formula.

**Key facts.** `FABL.two_mul_blrIndicator_sub_one`.
