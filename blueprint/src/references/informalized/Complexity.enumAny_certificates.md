<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumAny_certificates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificates Among Enumerated Ranks

**Claim.** Testing all ranks from zero through $2^w-1$, accepting rank $i$ exactly when $x$ concatenated with its width-$w$ little-endian binary word belongs to $V$, returns true exactly when some length-$w$ word $u$ makes $x$ concatenated with $u$ belong to $V$.

**Proof.** The consecutive-rank characterization (`Complexity.enumAny_iff`) turns a true result into a rank in the tested interval whose acceptance test is true. Since the interval starts at zero and has length $2^w$, that rank is less than $2^w$. The bounded-rank characterization of width-$w$ words (`Complexity.enumCandidates_iff`) then identifies existence of such an accepted rank with existence of a length-$w$ word accepted after concatenation with $x$. Membership in $V$ is exactly what the Boolean indicator tests.

**Key facts.** `Complexity.enumAny_iff`, `Complexity.enumCandidates_iff`.
