<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.mem_BPP_PTM_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Characterization

**Claim.** A language is in $\textsf{BPP}_{\mathrm{PTM}}$ exactly when it has a polynomial-time Boolean verifier using polynomially many random bits with acceptance and rejection probability at least $2/3$ on members and nonmembers, respectively.

**Proof.** This is the specialization of the parameterized characterization `mem_BPP_PTMWith_iff` to the constant probability function $p(n)=2/3$. Substituting this function into both sides gives exactly the stated BPP and verifier conditions.

**Key facts.** `Randomized.mem_BPP_PTMWith_iff`.
