<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.getD_append_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup after appending one value

**Claim.** For a list $vs$, an element $v$, and an index $j$, lookup in $vs$ with $v$ appended either agrees with lookup in $vs$ or returns $v$.

**Proof.** Compare $j$ with the length of $vs$. If $j$ is smaller, lookup in the appended list is unchanged. If $j$ equals the length, the lookup is the newly appended value. If $j$ is larger, both lookups use the default value, so they agree. These three cases establish the stated disjunction.
