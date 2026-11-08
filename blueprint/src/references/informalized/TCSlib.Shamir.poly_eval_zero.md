<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.poly_eval_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Secret at Zero

**Claim.** The sharing polynomial $s+Xq(X)$ evaluates to $s$ at zero.

**Proof.** At zero, the constant polynomial with value $s$ evaluates to $s$, while the factor $X$ evaluates to zero, so the term $Xq(X)$ vanishes. Therefore the polynomial evaluates to $s$.
