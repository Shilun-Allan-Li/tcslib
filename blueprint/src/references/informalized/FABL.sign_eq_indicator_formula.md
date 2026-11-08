<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.sign_eq_indicator_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Formula for Signs

**Claim.** For signs $b,x\in\{-1,1\}$, the indicator of $x=b$ equals $\frac{1+bx}{2}$.

**Proof.** Each sign is either $1$ or $-1$, so there are four cases. If $b=x$, then $bx=1$, and the right side is $1$, matching the indicator. If $b\ne x$, the signs are opposite, so $bx=-1$, and the right side is $0$, again matching the indicator.
