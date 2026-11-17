<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_multiply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Multiplication Run

**Claim.** Under the register bounds and zero-register hypotheses, the counter program has a bounded safe run from “product copy” to “power” that replaces register 7 by the product of its initial value and register 8, leaving the other registers and the empty result field as specified.

**Proof.** First copy the value of register 7 into register 11. The copy loop preserves the bound because the destination is initially zero and the source is at most $B$ (`Complexity.LogProg.registerCopy_loop`); the resulting vector is denoted $v_c$. Clear register 7, then put the original value of register 8 into register 10 and initialize register 7 to the desired product. The register-update bound shows these intermediate vectors remain bounded by $B$ (`Complexity.LogProg.register_update_le`).

Now run the multiplication body from “product test.” In that body, register 11 holds the original value of register 7, register 7 is zero, register 10 is zero, and register 6 is zero. The assumed product bound supplies the body's required output bound. The established multiplication-loop result therefore reaches “product clean,” with register 7 equal to the product and the temporary counters in the stated positions (`Complexity.comp_product`). Finally, clear registers 11 and 10. These clears preserve the bound, and the hypotheses that registers 10 and 11 were initially zero ensure that after cleanup the vector is exactly the original vector with register 7 replaced by the product. Each connecting transition preserves safety; composing the copy, setup, multiplication, and cleanup runs using the reachability composition and one-step principles (`Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.step`, and `Complexity.LogProg.AReach.single`) proves the result.

**Key facts.** `Complexity.LogProg.registerCopy_loop`, `Complexity.LogProg.register_update_le`, `Complexity.comp_product`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.single`.
