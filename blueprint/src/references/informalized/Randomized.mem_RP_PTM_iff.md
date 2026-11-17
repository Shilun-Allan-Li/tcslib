<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.mem_RP_PTM_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# RP Verifier Characterization

**Claim.** A language belongs to polynomial-time RP exactly when it has a polynomial-time verifier using polynomially many uniformly random bits, with acceptance probability at least $2/3$ on members and certain rejection on nonmembers.

**Proof.** The theorem identifies the two class definitions by rewriting polynomial-time RP as the equivalent formulation with acceptance threshold $2/3$ (the equality of classes `RP_PTM_eq_RP_PTMWith`). The membership characterization for that formulation says precisely that there is an efficient verifier with a polynomial random-bit bound, acceptance probability at least $2/3$ on members, and rejection on every random string for nonmembers (`mem_RP_PTMWith_iff`). Applying that characterization gives the stated equivalence.

**Key facts.** `Randomized.RP_PTM_eq_RP_PTMWith`, `Randomized.mem_RP_PTMWith_iff`.
