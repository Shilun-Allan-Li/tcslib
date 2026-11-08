<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrVal_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Binary Expansion

**Claim.** Interpreting the binary digits of any natural number with the first digit least significant gives the original number.

**Proof.** Use induction following the binary construction of natural numbers. The zero case has empty binary digits and value zero. In the inductive step, the binary digits of the number obtained by appending a bit $b$ are the previous digits followed by $b$. The value of this list is the contribution of the new bit, $1$ when $b$ is true and $0$ otherwise, plus twice the previous value. By the induction hypothesis and the defining value of a number with appended binary bit, this is exactly the number represented.
