<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_membership_of_verifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tautology complements and coNP

**Claim.** If the language recognized by the verifier belongs to polynomial time, then the language of binary strings whose decoded DNF is a tautology belongs to coNP.

**Proof.** Use certificate length parameters $C=c=1$ and take the verifier language itself as the polynomial-time witness language. For any input $x$, the complement of tautology membership is equivalent to the existence of a word $u$ of length $|x|+1$ for which the decoded DNF evaluates to false under the assignment determined by $u$ (the certificate characterization, `Complexity.taut_certificate_equiv`). For each such certificate, the verifier accepts the concatenation $x++u$ exactly when that evaluation is false (`Complexity.taut_verifier_append`). Thus the certificate condition in the definition of NP for the complement of the tautology language is equivalent to membership of $x$ in that complement. Since the verifier language is in P by hypothesis, this establishes that the complement is in NP, and hence the tautology language is in coNP.

**Key facts.** `Complexity.taut_certificate_equiv`, `Complexity.taut_verifier_append`.
