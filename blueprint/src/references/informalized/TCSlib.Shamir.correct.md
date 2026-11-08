<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Shamir sharing

**Claim.** For $k>0$, reconstruction from any set of at least $k$ parties returns the secret shared by the Shamir scheme, for every secret and every allowed randomness polynomial.

**Proof.** Fix a set $A$ of at least $k$ parties, a secret, and an allowed randomness polynomial $q$. The sharing polynomial has degree less than $k$ (`TCSlib.Shamir.degree_poly_lt`), so the size bound gives degree less than $|A|$. Party labels are distinct (`TCSlib.Shamir.label_injective`), and the shares are evaluations of the sharing polynomial at those labels. By uniqueness of interpolation at distinct points, the polynomial interpolating the shares on $A$ is the sharing polynomial itself. Reconstruction evaluates this interpolant at zero; the sharing polynomial's value there is the secret (`TCSlib.Shamir.poly_eval_zero`).

**Key facts.** `TCSlib.Shamir.degree_poly_lt`, `TCSlib.Shamir.label_injective`, `TCSlib.Shamir.poly_eval_zero`.
