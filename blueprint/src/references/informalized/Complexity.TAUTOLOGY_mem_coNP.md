<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.TAUTOLOGY_mem_coNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tautology Belongs to coNP

**Claim.** The language of bit strings whose decoded DNF formula is true under every Boolean assignment belongs to coNP; equivalently, its complement belongs to NP.

**Proof.** The proof applies the verifier characterization for Tautology: if the associated verifier language is in polynomial time, then Tautology belongs to coNP ($\texttt{taut_membership_of_verifier}$). The required polynomial-time membership of that verifier is supplied by $\texttt{taut_verifier_mem_P}$.

**Key facts.** `Complexity.taut_verifier_mem_P`, `Complexity.taut_membership_of_verifier`.
