<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecWord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Boolean Code

**Claim.** For finite $\alpha$, every natural number $L$, and $a:\alpha\to\{\mathrm{false},\mathrm{true}\}$, the Boolean list encoding $a$ with length parameter $L$ has length exactly $L$.

**Proof.** The encoding is formed by applying the list constructor `List.ofFn` to a function on the indices of the finite type of size $L$. Such a list has one entry for each index, so its length is $L$.
