<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/ModelInvariance.lean :: Complexity.mem_DTIME_of_decidesInTimeVia -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Time Classes Under Alphabet Encoding

**Claim.** A language decidable in time $T(n)$ by a machine on inputs encoded symbolwise over a finite alphabet belongs to binary $[0mDTIME(n\mapsto T(n)+1)$.

**Proof.** Apply the alphabet-reduction theorem (`Turing.FinTM.alphabet_reduction`) to the given machine, the injective encoding of binary symbols, and the function that returns the one-symbol list containing the language indicator. The hypothesis that the original machine computes this output within $T(n)$ steps is exactly the assumed encoded-input computation. The theorem supplies a binary-alphabet machine and a constant $c$ that compute the same output within $c(T(n)+1)$ steps. This is precisely membership in the stated time class.

**Key facts.** `Turing.FinTM.alphabet_reduction`.
