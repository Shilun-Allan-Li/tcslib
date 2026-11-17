<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.length_lbStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for the Suffix Step

**Claim.** For every finite bit string $s$, the length of its suffix step is at most $\max(|s|,2)$.

**Proof.** Apply the length bound for pair encodings with dropped prefixes (`Complexity.length_pairEncode_drop_le`) using $i=0$ for the first decoded component and $j=1$ for the second. The resulting encoded pair is exactly the suffix step of $s$, so the stated bound follows directly.

**Key facts.** `Complexity.length_pairEncode_drop_le`.
