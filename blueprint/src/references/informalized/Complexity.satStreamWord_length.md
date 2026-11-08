<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamWord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Encoded Seam State

**Claim.** For every streaming seam state with fresh cursor $f$, consumed length $c$, and phase value $q$, the encoded seam word has length $2f+2c+q+4$.

**Proof.** Each pair encoding duplicates every bit of its first component, then appends the two-bit separator $[\mathrm{false},\mathrm{true}]$ and its second component. Thus the inner encoding, whose first component has $c$ true bits and whose second has $q$ true bits, has length $2c+2+q$. The outer encoding duplicates the $f$ true bits and appends another two-bit separator and that inner encoding. Its length is therefore $2f+2+(2c+2+q)=2f+2c+q+4$.
