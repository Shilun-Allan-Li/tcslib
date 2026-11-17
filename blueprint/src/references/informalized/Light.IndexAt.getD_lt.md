<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.IndexAt.getD_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a List Entry

**Claim.** Under the stated hypotheses on the length, indexed values, entry bounds, and endpoint of the list, every entry indexed by $i<N$ is less than $p$, including when the entry is expressed using the default-zero list lookup.

**Proof.** The length hypothesis identifies the list length with $N$, so $i<N$ is a valid list index. The entry returned by default-zero lookup is therefore the actual entry at index $i$. That entry belongs to the list, and the assumed bound on every list member gives that it is less than $p$.
