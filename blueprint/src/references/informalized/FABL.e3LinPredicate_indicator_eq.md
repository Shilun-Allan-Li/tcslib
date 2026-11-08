<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.e3LinPredicate_indicator_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three Sign Equation Indicator

**Claim.** For a sign $b$ and three signs $y_0,y_1,y_2$, the indicator that $y_0y_1y_2=b$ equals $(1+b y_0y_1y_2)/2$, identifying each sign with its real value.

**Proof.** Each of $b,y_0,y_1,y_2$ is either $1$ or $-1$. Split into these finitely many possibilities. If $y_0y_1y_2=b$, then $b y_0y_1y_2=1$, so the right side is $1$; otherwise the product of the four signs is $-1$, so the right side is $0$. These are exactly the two values of the indicator.
