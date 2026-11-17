<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeBitsNat_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the binary expansion

**Claim.** Interpreting the canonical least-significant-bit-first binary expansion of any natural number as a binary numeral gives that number.

**Proof.** Induct on the binary construction of natural numbers. For zero, its binary expansion evaluates to zero. In the successor construction, the binary expansion is obtained by appending the new bit to the expansion of the smaller number. By the induction hypothesis, folding the smaller expansion evaluates to that smaller number; applying the corresponding binary-bit operation therefore gives precisely the value of the constructed number.
