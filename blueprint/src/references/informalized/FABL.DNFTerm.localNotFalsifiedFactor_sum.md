<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.DNFTerm.localNotFalsifiedFactor_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Nonfalsification Factor Sum

**Claim.** For a coordinate in the support of a term, the weighted sum of its local nonfalsification factor over the three restriction states is $3/4$. For a coordinate outside the support, the sum is $1$.

**Proof.** Split according to whether $i$ belongs to the support. If it does, the selected literal at $i$ has a local factor equal to $1$ precisely when it is not falsified, and $0$ otherwise. The weighted sum of this factor over the three restriction states is $3/4$, by the one-literal weighted nonfalsification identity (`literal_not_falsified_local_weight`). If $i$ is outside the support, its local factor is $1$ in every restriction state, so the sum is just the sum of the three state weights, which is $1$ (`sum_coordRestrictionWeight`).

**Key facts.** `FABL.literal_not_falsified_local_weight`, `FABL.sum_coordRestrictionWeight`.
