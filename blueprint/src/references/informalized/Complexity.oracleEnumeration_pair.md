<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.oracleEnumeration_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing preserves oracle decoding

**Claim.** For all natural numbers $j$ and $r$, decoding the oracle-machine index obtained by pairing $j$ and $r$ gives the machine decoded from $j$.

**Proof.** The oracle enumeration first takes the first component of the unpairing of its index and decodes that component. Unpairing the paired index $(j,r)$ returns $j$ as its first component. Substituting this into the enumeration therefore gives exactly the machine decoded from $j$.
