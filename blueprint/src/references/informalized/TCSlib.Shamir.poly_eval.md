<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.poly_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Sharing Polynomial

**Claim.** For every $a\in F$, the polynomial $s+Xq(X)$ evaluates to $s+a q(a)$.

**Proof.** Evaluation preserves addition and multiplication, and the constant polynomial with value $s$ evaluates to $s$. The polynomial $X$ evaluates at $a$ to $a$, so the product $Xq(X)$ evaluates to $a q(a)$. Adding these evaluations gives the stated formula.
