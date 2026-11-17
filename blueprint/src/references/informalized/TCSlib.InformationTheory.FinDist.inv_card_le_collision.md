<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.inv_card_le_collision -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on Collision Probability

**Claim.** For every probability distribution $p$ on a finite set $\alpha$, its collision probability $\sum_{a\in\alpha}p(a)^2$ is at least $1/|\alpha|$.

**Proof.** The set is nonempty: a probability distribution has total mass one, so its finite underlying set cannot be empty. Thus $|\alpha|>0$. The Cauchy–Schwarz inequality for finite sums gives $(\sum_a p(a))^2\le |\alpha|\sum_a p(a)^2$. Since the total mass is one, this becomes $1\le |\alpha|\operatorname{Coll}(p)$. Dividing by the positive cardinality yields the claimed lower bound.

**Key facts.** `TCSlib.InformationTheory.FinDist.card_pos`.
