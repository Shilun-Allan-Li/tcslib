<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.lbStep_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the Suffix Step

**Claim.** For bit strings $u$ and $v$ and a natural number $i$, iterating the suffix step $i$ times on the encoding of $(u,v)$ yields the encoding of $(u,v.drop\ i)$.

**Proof.** Induct on $i$. At zero iterations, the statement is the identity. For the successor step, apply one suffix step after the $i$ iterations supplied by the induction hypothesis. On an encoded pair, the suffix step preserves the first component and removes the first bit of the second. Removing one more bit after dropping the first $i$ bits is the same as dropping $i+1$ bits, by the composition law for list drops. This gives the claimed encoding.
