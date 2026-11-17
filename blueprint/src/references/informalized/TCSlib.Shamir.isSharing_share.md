<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.isSharing_share -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shamir shares form a sharing

**Claim.** For $k>0$, the shares produced from a secret and an allowed randomness polynomial in the Shamir scheme share that secret with degree bound less than $k$.

**Proof.** Use the Shamir sharing polynomial as the witness. Its degree is less than $k$ (`TCSlib.Shamir.degree_poly_lt`), and its value at zero is the secret (`TCSlib.Shamir.poly_eval_zero`). By definition, each party's share is the evaluation of this polynomial at that party's label. Since $k>0$, the bound parameter $k-1$ satisfies $(k-1)+1=k$, so the polynomial's degree is less than the required bound.

**Key facts.** `TCSlib.Shamir.degree_poly_lt`, `TCSlib.Shamir.poly_eval_zero`.
