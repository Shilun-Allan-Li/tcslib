<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Halting.lean :: Complexity.HALT_pairEncode_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting on an Encoded Pair

**Claim.** The halting function returns true on the pairing encoding of $\alpha$ and $x$ if and only if the machine decoded from $\alpha$ produces some output on input $x$ within finitely many steps.

**Proof.** Apply the general characterization of the halting function (Complexity.HALT_eq_true_iff) to the encoded input. In the forward direction, it supplies some pair $(\alpha',x')$ encoding that same input, together with a finite-time computation. Injectivity of the pairing encoding (Turing.pairEncode_injective) forces $(\alpha',x')=(\alpha,x)$, so this is the desired computation. Conversely, any such computation witnesses the existential characterization directly by choosing the given $lpha,x$.

**Key facts.** `Complexity.HALT_eq_true_iff`, `Turing.pairEncode_injective`.
