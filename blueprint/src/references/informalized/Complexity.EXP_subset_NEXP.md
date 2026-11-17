<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.EXP_subset_NEXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Time Is Contained in Nondeterministic Exponential Time

**Claim.** Every language in $\mathrm{EXP}$ belongs to $\mathrm{NEXP}$, with membership characterized by a polynomial-time verifier and certificates of the specified exponential length.

**Proof.** Take a language in $\mathrm{EXP}$, witnessed by an exponent $c$, a constant-factor time bound, and a deterministic decider. The construction `a3_verifier_mem_P` supplies a language in $\mathrm{P}$ that verifies membership using a certificate of length $2^{(|x|+1)^c}$. For the forward implication, if $x$ belongs to the language, choose the certificate consisting of exactly that many zeros. Its length has the required form (the certificate multiplier is $1$), and `a3_verifier_append` says that appending it to $x$ places the result in the verifier language. Conversely, for any certificate of the required length, membership of the concatenation in the verifier language implies $x$ belongs to the original language, again by `a3_verifier_append`. These witnesses give the defining $\mathrm{NEXP}$ representation.

**Key facts.** `Complexity.a3_verifier_mem_P`, `Complexity.a3_verifier_append`.
