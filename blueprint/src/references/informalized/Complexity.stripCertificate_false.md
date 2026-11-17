<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.stripCertificate_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stripping an All-Zero String

**Claim.** For every natural number $k$, stripping the binary string of $k$ zeros is undefined.

**Proof.** Proceed by induction on $k$. For $k=0$, the string is empty and stripping is undefined by definition. For the successor case, the string consists of a leading zero followed by $k$ zeros. By the induction hypothesis, stripping the tail is undefined; the definition then returns an undefined result for a leading zero as well.
