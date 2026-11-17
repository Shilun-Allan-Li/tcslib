<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productRetentionCoordinatePairPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joint coordinate-pair mass

**Claim.** For any two states, the joint mass under the retention-and-resampling experiment is the initial mass of the first state times the conditional noise mass of the second state given the first.

**Proof.** Expand the bind and map defining the joint experiment as finite sums. At the specified pair $(x,y)$, the map contributes only when the starting state is $x$ and the generated state is $y$. Thus the sum over starting states collapses to its $x$ term, and the inner sum over generated states collapses to its $y$ term. Their product is $\pi(x)$ times the coordinate-noise mass of $y$ given $x$, as claimed.
