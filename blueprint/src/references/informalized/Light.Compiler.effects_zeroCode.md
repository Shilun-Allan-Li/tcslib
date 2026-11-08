<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.effects_zeroCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zeroing the Stack Cells

**Claim.** If the constant-one cell contains the word representation of $1$, then for every $x<F$, executing the zeroing code leaves the stack cell at index $4+x$ containing the word representation of $0$.

**Proof.** Induct on $F$. The assertion is vacuous for $F=0$. In the successor case, the code is the earlier zeroing code followed by a subtraction into the newly added stack cell (`zeroCode_succ`). The earlier code preserves the constant-one cell: all its instructions write only within the main frame, by `writesIn_zeroCode`, and the general preservation fact for effects (`agreeOutside_effects`) therefore lets us read the original value $1$ afterward (`AgreeOutside.read`). Subtracting that value from itself writes zero to the new cell (`effect_sub`). If $x$ is this final index, the update gives the result directly; if $x<F$, the last instruction updates a different address, so the induction hypothesis gives the result.

**Key facts.** `Light.Compiler.zeroCode_succ`, `Light.Compiler.writesIn_zeroCode`, `WordRAM.agreeOutside_effects`, `WordRAM.AgreeOutside.read`, `WordRAM.effect_sub`, `WordRAM.effects_append`.
