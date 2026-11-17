<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Defs.lean :: TCSlib.SecretSharing.AccessStructure.threshold_auth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Authorization Criterion

**Claim.** In the threshold access structure with threshold $k$, a finite set $A$ is authorized exactly when its cardinality is at least $k$.

**Proof.** The threshold structure defines authorization of $A$ by the condition $k\leq \#A$. Therefore the asserted equivalence is precisely this definition.
