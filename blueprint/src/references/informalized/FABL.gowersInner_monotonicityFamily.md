<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersInner_monotonicityFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity Family Inner Product

**Claim.** The Gowers inner product of the family that equals $f$ on the zero last-coordinate slice and $1$ on the other slice equals the dimension-$k$ diagonal inner product of $f$.

**Proof.** Use the successor-dimensional decomposition (FABL.gowersInner_succ), which writes the inner product as an average over $y$ of the product of the two half expectations. For the zero slice, the monotonicity family contributes $f$ at every factor, so its half expectation is the average over $x$ of the product of $f$ over the remaining cube points. For the one slice, every factor is $1$, so that half expectation is $1$. The product of the slice expectations is thus the zero-slice expectation. Averaging this over $y$ is exactly the definition of the diagonal inner product in dimension $k$.

**Key facts.** `FABL.gowersInner_succ`.
