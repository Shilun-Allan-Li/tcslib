<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_bits_codeBitsNat_append_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a One in Binary Encoding

**Claim.** The binary expansion of the natural number encoded by appending $1$ to a finite bit string $s$ is exactly $s$ followed by $1$.

**Proof.** Let the digits corresponding to the bits of $s$ followed by $1$ be obtained by replacing false with $0$ and true with $1$. The base-two digit theorem `Nat.digits_ofDigits` says that converting these digits to a number and then taking its base-two digits recovers the original digit list; its hypotheses hold because every digit is either $0$ or $1$, and the final digit is nonzero. The identity `ntc_codeBitsNat_eq_ofDigits` identifies the number encoded by the bit string with this base-two numeral, while `Nat.digits_two_eq_bits` identifies its base-two digits with its binary expansion. Thus the binary expansion is the mapped digit list. Since mapping the false/true-to-zero/one conversion back to Boolean bits is injective, this list is exactly $s$ followed by $1$.

**Key facts.** `Complexity.ntc_codeBitsNat_eq_ofDigits`.
