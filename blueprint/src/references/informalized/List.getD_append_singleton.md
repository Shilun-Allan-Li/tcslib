<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_append_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Default Lookup After Appending One Element

**Claim.** Appending $a$ to $l$ changes the default-lookup function only at position $\operatorname{length}(l)$, where its value becomes $a$.

**Proof.** Fix a position $e$ and compare it with $\operatorname{length}(l)$. If $e$ is smaller, lookup in the appended list agrees with lookup in $l$, and the update at the length does not affect the value. If $e$ equals the length, lookup after appending returns the new final entry $a$, exactly the updated value. If $e$ is larger, both lookups return the default, since the position is out of range in both lists; the update again does not affect it. Thus the two functions agree at every position.
