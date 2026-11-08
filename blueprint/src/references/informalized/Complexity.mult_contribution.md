<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_contribution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A diagonal multiplication contribution

**Claim.** From a diagonal-processing configuration, the program reaches the next-$b$ state, with only register 11 changed, by adding the indicated product of input bits when the two indices agree.

**Proof.** The diagonal state first tests whether the diagonal index in register 10 equals the current column in register 7. If not, it advances directly to the next-$b$ state without changing registers. If they agree, the program queries the input-bit oracle at the address in register 0. When that bit is zero, its contribution is zero and the program proceeds without further changes. When it is one, the program queries the bit at the address in register 9. A zero second bit again contributes zero; if both bits are one, the add state increments register 11 once. The whole-input query representation is exactly the encoded query for the bit at the selected address (`vword_whole₁`), and the oracle returns the corresponding input bit (`mult_queries`). The resulting register update is therefore precisely the old value plus the stated conditional product. Each intermediate configuration meets the required bound and program preconditions (`mult_preconditions`), so the one-step executions combine into the claimed reachability (`AReach.step`, `AReach.single`, `AReach.refl`).

**Key facts.** `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.vword_whole₁`, `Complexity.mult_preconditions`, `Complexity.mult_queries`.
