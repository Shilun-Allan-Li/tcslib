<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardTseitin.lean :: Complexity.TQBFHard.length_le_length_flatMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flat-map length bound

**Claim.** If $a$ occurs in $l$, then the length of $f(a)$ is at most the length of the list obtained by concatenating $f(x)$ over the entries of $l$.

**Proof.** Induct on $l$. The empty list case is impossible because $a$ cannot occur there. For a nonempty list $b::l$, its flattened image is $f(b)$ followed by the flattening of $l$, so its length is the sum of those two lengths. If $a=b$, the first summand is the desired length and the inequality follows. Otherwise $a$ occurs in $l$; the induction hypothesis bounds the length of $f(a)$ by the length of the tail flattening, which is at most the full sum.
