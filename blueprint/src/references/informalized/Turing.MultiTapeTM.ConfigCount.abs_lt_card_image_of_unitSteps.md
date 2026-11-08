<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Position bound from unit steps

**Claim.** If an integer-valued sequence starts at zero and each successive change has absolute value at most one, then every value among its first $t+1$ terms has absolute value strictly less than the number of distinct values among those terms.

**Proof.** Take $z$ in the image of the sequence over indices $0$ through $t$, and choose $t'\le t$ with $p(t')=z$. The unit-step reachability fact (`exists_eq_of_between`) says that every integer between $0$ and $p(t')$ is attained at some index at most $t'$. Thus every integer in the inclusive interval from $\min(0,z)$ to $\max(0,z)$ belongs to the image over indices through $t$. This interval has $|z|+1$ elements, so the image has at least $|z|+1$ distinct values. Therefore $|z|$ is strictly less than the image’s cardinality.

**Key facts.** `Turing.MultiTapeTM.ConfigCount.exists_eq_of_between`.
