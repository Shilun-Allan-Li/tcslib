<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.inBPPWith_iff_inBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Error BPP Characterization

**Claim.** A language has the fixed success-probability bound $2/3$ in the polynomial-time verifier definition exactly when it belongs to standard BPP.

**Proof.** Both sides quantify over the same polynomial-time verifier, the same polynomial number of random bits, and the same two correctness conditions. The function supplying the success threshold on the left is constantly $2/3$, exactly the threshold in the definition of standard BPP. Thus the two propositions are identical.
