<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.composedMajoritySplitPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of the Split Majority Distribution

**Claim.** For each $m\ge 0$, $p\in[0,1]$, and split input $(h,t)$, its probability mass under the split distribution is the product of the probability masses of $h$ and $t$ under their respective product distributions.

**Proof.** Expand the mass of $(h,t)$ under the distribution formed by first sampling the head and then sampling and mapping the tail to the pair with that head. The finite sum over all possible heads has only one nonzero contribution: the head equal to $h$, since every other head produces pairs with a different first coordinate. For that head, the finite sum over tails likewise has only one nonzero contribution, namely $t$, because any other tail has a different second coordinate. The surviving term is exactly the product of the head mass at $h$ and the tail mass at $t$.
