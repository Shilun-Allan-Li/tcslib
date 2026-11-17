<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_fourth_eq_expect_odd_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-Moment Decomposition

**Claim.** If adjoining a first sign $b$ gives $f(b,x)=b d(x)+e(x)$, then the fourth moment of $f$ equals the fourth moment of $d$, plus six times the average of $d^2e^2$, plus the fourth moment of $e$.

**Proof.** Split the average over the $(n+1)$-dimensional cube into its two first-coordinate slices (`expect_fin_cons`). On the slice with first sign $1$, the hypothesis gives $f=d+e$; on the slice with sign $-1$, it gives $f=-d+e$. Thus the average is the average over $x$ of $\big((d(x)+e(x))^4+(-d(x)+e(x))^4\big)/2$. Expanding the two fourth powers cancels the terms with odd powers of $d$, leaving $d(x)^4+6d(x)^2e(x)^2+e(x)^4$. Finally, distribute the average across the sum and pull the constant factor $6$ outside. The resulting expression is the stated decomposition.

**Key facts.** `FABL.expect_fin_cons`.
