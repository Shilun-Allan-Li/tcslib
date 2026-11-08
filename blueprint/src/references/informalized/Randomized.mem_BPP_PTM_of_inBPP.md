<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.mem_BPP_PTM_of_inBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier Recognition in BPP

**Claim.** If a language has a polynomial-time verifier with polynomially many random bits that accepts members and rejects nonmembers with probability at least $2/3$, then it belongs to $\textsf{BPP}_{\mathrm{PTM}}$.

**Proof.** Apply the parameterized implication `mem_BPP_PTMWith_of_inBPPWith` with the constant probability function $p(n)=2/3$. The hypothesis is precisely the verifier guarantee at this probability, and the conclusion specializes to membership in $\textsf{BPP}_{\mathrm{PTM}}$.

**Key facts.** `Randomized.mem_BPP_PTMWith_of_inBPPWith`.
