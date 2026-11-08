<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.majorityThreeValue_neg_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-input majority indicator identity

**Claim.** For signs $a,b,c\in\{-1,1\}$, the indicator that their three-input majority is $-1$ equals the sum of the three pairwise products of the indicators that each sign is $-1$, minus twice the product of all three indicators.

**Proof.** Each sign is either $1$ or $-1$, so split into the eight possible triples. The majority is $-1$ exactly when at least two of the signs are $-1$. If exactly two are negative, exactly one pairwise product of the three negative-sign indicators is $1$, and the triple product vanishes; both sides are $1$. If all three are negative, the right side is $3-2=1$, again matching the majority indicator. If at most one sign is negative, every pairwise product and the triple product vanish, and the majority is $1$, so both sides are $0$.
