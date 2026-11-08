<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.char_s_conj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjugate character identity

**Claim.** The complex conjugate of the character at frequency $s$, evaluated at $x$, equals the character at frequency $-s$ evaluated at $x$.

**Proof.** Negating the frequency negates its dot product with $x$ (`ZkFourier.zkDot_neg_left`). The root-of-unity map sends a negated residue to the complex conjugate of its value (`ZkFourier.toOmega_neg`). Combining these identities gives the claimed equality.

**Key facts.** `ZkFourier.zkDot_neg_left`, `ZkFourier.toOmega_neg`.
