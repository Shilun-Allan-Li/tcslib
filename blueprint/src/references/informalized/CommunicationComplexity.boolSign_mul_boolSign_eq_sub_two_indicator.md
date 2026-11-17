<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.boolSign_mul_boolSign_eq_sub_two_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of Boolean signs

**Claim.** For Boolean values $a$ and $b$, the product of their signs is $1-2\mathbf{1}[a\ne b]$: it is $1$ when they agree and $-1$ when they differ.

**Proof.** There are four cases. If both bits are false, the signs multiply to $1$, and the indicator is $0$. If exactly one bit is true, the signs multiply to $-1$, and the indicator is $1$. If both are true, the signs again multiply to $1$, and the indicator is $0$. In each case the product equals the stated expression.
