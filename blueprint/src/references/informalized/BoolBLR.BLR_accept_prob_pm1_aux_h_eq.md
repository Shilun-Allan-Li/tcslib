<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.BLR_accept_prob_pm1_aux_h_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The BLR Acceptance Indicator

**Claim.** For the \{-1,1\} lift of a Boolean function, the indicator that the BLR multiplicative check accepts equals one half of one plus the product of the three lifted values.

**Proof.** Fix $x,y$ and split according to whether the two sides of the multiplicative check are equal. In the accepting case, the lifted value at $x\oplus y$ equals the product of the lifted values at $x$ and $y$. Each lifted value is $1$ or $-1$, so their triple product is $1$; the right-hand side is therefore $(1+1)/2=1$, matching the indicator. In the rejecting case, these signs are unequal, hence opposite, and their triple product is $-1$. The right-hand side is then $(1-1)/2=0$, again matching the indicator.
