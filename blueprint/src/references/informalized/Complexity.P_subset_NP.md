<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.P_subset_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial time lies in nondeterministic polynomial time

**Claim.** Every language in $\mathsf{P}$ belongs to $\mathsf{NP}$, with membership witnessed by a polynomial-time verifier and certificates of the prescribed length.

**Proof.** For a language $L\in\mathsf{P}$, use $L$ itself as the verifier and choose $C=c=0$. The required certificate length is then zero, so the only possible certificate is the empty string. Appending it leaves the input unchanged; therefore $x\in L$ holds exactly when there exists such a certificate whose concatenation with $x$ belongs to $L$. Since the verifier is $L$, it is in $\mathsf{P}$, as required.
