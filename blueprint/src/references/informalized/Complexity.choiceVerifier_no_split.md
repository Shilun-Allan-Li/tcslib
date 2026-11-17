<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choiceVerifier_no_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Split Implies Nonmembership

**Claim.** If the bounded search finds no $n$ with $n+(C+1)(n+1)^c=|y|$, then $y$ is not in the verifier language.

**Proof.** Suppose instead that $y$ belongs to the verifier language, witnessed by a split $y=xu$ with $|u|=C(|x|+1)^c$. Taking lengths gives $|y|=|x|+C(|x|+1)^c$. Setting $n=|x|$ rewrites this as $n+(C+1)(n+1)^c=|y|$. The characterization of a failed split search (`Complexity.certificateSplit_none_iff`) says no such natural number can exist, a contradiction.

**Key facts.** `Complexity.certificateSplit_none_iff`.
