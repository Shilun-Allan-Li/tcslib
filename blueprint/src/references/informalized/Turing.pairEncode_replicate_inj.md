<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairEncode_replicate_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity for Unary First Components

**Claim.** If the encodings of $(1^n,u)$ and $(1^{n'},u')$ agree, then $n=n'$ and $u=u'$.

**Proof.** Injectivity of pair encoding first gives equality of the first components, $1^n=1^{n'}$, and equality of the tails, $u=u'$. Taking lengths in the first equality yields $n=n'$, since a string of $n$ repeated ones has length $n$.

**Key facts.** `Turing.pairEncode_injective`.
