<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.getD_append_singleton_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup at the appended value

**Claim.** At index equal to the length of $vs$, lookup in $vs$ with $v$ appended, using $0$ as the default, returns $v$.

**Proof.** Appending one element places it at the index immediately following the entries of $vs$. Thus the lookup at index $|vs|$ returns the appended value $v$.
