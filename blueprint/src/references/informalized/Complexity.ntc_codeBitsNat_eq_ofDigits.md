<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_codeBitsNat_eq_ofDigits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit Encoding and Base-Two Digits

**Claim.** The least-significant-bit-first value of a finite bit string equals the base-two numeral obtained by replacing false by $0$ and true by $1$.

**Proof.** Induct on the list of bits. For the empty list both values are zero. For a list with first bit $b$ and tail $w$, its bit-fold value is obtained by applying the binary constructor for $b$ to the value of the tail. If $b$ is false, this is twice the tail's value; if $b$ is true, it is twice that value plus one. The base-two numeral of the digit list has the same recurrence: its leading digit contributes respectively zero or one times the appropriate power of two, with the tail contributing twice its value. Applying the induction hypothesis identifies the tail values, and the two cases give the equality.
