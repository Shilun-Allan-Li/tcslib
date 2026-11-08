<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopValue_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Binary Digits

**Claim.** For every natural number n, the little-endian Boolean word of its binary digits has counter value n.

**Proof.** Use the binary recursion for natural numbers. At zero, the binary word is empty and its counter value is zero. In the recursive bit case, write the binary digits of the number obtained by appending bit b to the digits of n. The bit-appending identity (`Nat.bits_append_bit`) expresses this word as the digits of n with b appended. By the definition of the counter value, appending b changes the value to twice the previous value plus 1 if b is true, and plus 0 otherwise. The induction hypothesis identifies the previous value with n, and the binary bit-value identity (`Nat.bit_val`) identifies the resulting number with the number represented by the appended word. Thus the counter value is the original number.
