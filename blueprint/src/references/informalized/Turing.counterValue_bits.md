<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterValue_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the binary digit word

**Claim.** For every natural number $t$, the binary value of the binary digit word of $t$ is $t$.

**Proof.** The binary value of a Boolean word can be expressed as the fold that reads its bits using the natural-number bit operation (`foldr_bit_eq_ofDigits`). Applied to the binary digit word of $t$, this identifies its digit value with the code of that word. The coding theorem `codeBitsNat_bits` says that the code of the binary digit word of $t$ is exactly $t$, proving the equality.

**Key facts.** `Turing.foldr_bit_eq_ofDigits`, `Turing.codeBitsNat_bits`.
