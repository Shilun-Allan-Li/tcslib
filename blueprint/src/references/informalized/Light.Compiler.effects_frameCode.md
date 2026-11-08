<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.effects_frameCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effects of Frame Code

**Claim.** Given the stated initial values, executing the frame code sets the frame pointer to the stack address for index $4$, zeros the first $F$ local stack cells, then writes $i$ and $j$ to the next two stack cells in order.

**Proof.** The zeroing code writes only within the first $F$ local cells (`Light.Compiler.writesIn_zeroCode`). Therefore it leaves the zero, pool, and argument cells unchanged, since those addresses are outside that region and distinct from the frame pointer. This follows from the general preservation theorem for instruction lists and its pointwise consequence (`WordRAM.agreeOutside_effects`, `WordRAM.AgreeOutside.cell`). Thus, after setting the frame pointer, the zero and argument cells still hold their assumed values. The first instruction computes $0-2\cdot4$, which is the stack address for index $4$, and writes it to the frame pointer (`WordRAM.effect_sub`). After the zeroing code, the next instruction adds the first argument to zero and stores the result at stack index $5$; the final instruction adds the second argument to zero and stores it at stack index $6$ (`WordRAM.effect_add`). The list-effect concatenation law identifies these stages in their execution order (`WordRAM.effects_append`).

**Key facts.** `Light.Compiler.writesIn_zeroCode`, `WordRAM.agreeOutside_effects`, `WordRAM.AgreeOutside.cell`, `WordRAM.effect_sub`, `WordRAM.effect_add`, `WordRAM.effects_append`.
