<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.inBPP_of_mem_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Randomized Machines Yield BPP

**Claim.** If a language is decided by a finite nondeterministic machine with a polynomial time bound on every choice string and correctness probability at least $2/3$, then it belongs to BPP in the polynomial-time verifier model.

**Proof.** The general conversion theorem for nondeterministic polynomial-time machines states that any such machine with per-input correctness probability at least $p(n)$ yields a polynomial-time verifier with the same bound (\texttt{Randomized.inBPPWith\_of\_mem\_BPP\_PTMWith}). Apply it with the constant function $p(n)=2/3$. Its hypotheses are exactly the stated polynomial time bound, halting on each prescribed-length choice string, and $2/3$ correctness probability; its conclusion is membership in BPP.

**Key facts.** `Randomized.inBPPWith_of_mem_BPP_PTMWith`.
