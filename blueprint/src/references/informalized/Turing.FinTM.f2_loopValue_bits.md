<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopValue_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Binary Bit List

**Claim.** For every natural number $n$, evaluating the recursively defined value of the bit list $n.\mathrm{bits}$ gives $n$.

**Proof.** Use the binary recursion principle for natural numbers. At $n=0$, the bit list has value zero by the defining equation for the value function. In the recursive step, write $n$ as the result of appending a bit $b$ to the binary representation of a smaller number. The bit-list append formula (`Nat.bits_append_bit`) identifies this representation; evaluating its leading bit gives twice the value of the shorter list, plus $1$ if $b$ is true and $0$ otherwise. By the induction hypothesis the shorter list has value $n$, so this is exactly the value represented by the new bit, by the defining formula for binary bits (`Nat.bit_val`).
