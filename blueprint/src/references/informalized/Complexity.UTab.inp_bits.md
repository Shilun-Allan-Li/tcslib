<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.inp_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Cell Encoding

**Claim.** Under the stated register, phase, layout, and validity assumptions, executing the input-cell template produces exactly the tableau instruction bits at position $e.i$.

**Proof.** First use the preceding-cell relation to identify the previous input instruction. Since $t\ne 0$ and $e.i$ is the input position at time $t$, the equality $e.q+\mathrm{stride}=e.i$ implies $e.q$ is the input position at time $t-1$; this is the arithmetic fact supplied by `prev_eq`. Thus the register values give the current and previous input positions required by the input source list. The position bound ensures that $e.i$ lies within the tableau step and that `cfgPos` identifies it as the input position $(t,p)$ (`inpIdx_lt_succ`, `cfgPos_inpIdx`).

Next, the phase hypothesis identifies the template’s source list with the prescribed input-cell sources. Evaluating those sources at the register record gives precisely `inpSrcs`: the layout source supplies the hard-wired bit in its specified range and is false outside it, while the remaining sources refer to the current, preceding, and following input cells as prescribed. The source evaluation identity is `inpS_toBitSrc`; padding preserves that identity, by `padS_toBitSrc`. The assumptions also make every source valid: the register bounds establish validity of the neighboring-cell and current-cell references, the step-start register establishes validity of snapshot references, and the layout hypothesis supplies validity for the layout source. The input-source validity criterion is `ok_inpS`, and padding preserves it by `ok_padS`.

Finally, the instruction-level execution theorem applies: because `cfgInstr` at $e.i$ has the input template’s kind and padded prescribed sources, and the evaluated template sources agree with those sources, `prog_instr_bits` identifies the output of the template operations with the encoded tableau instruction bits.

**Key facts.** `Complexity.UTab.prev_eq`, `Complexity.inpIdx_lt_succ`, `Complexity.cfgPos_inpIdx`, `Complexity.length_tabLayout`, `Complexity.UTab.inpS_toBitSrc`, `Complexity.UTab.padS_toBitSrc`, `Complexity.UTab.ok_inpS`, `Complexity.UTab.ok_padS`, `Complexity.UTab.prog_instr_bits`.
