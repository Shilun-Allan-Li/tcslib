<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.steps_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup execution

**Claim.** If $-1$ satisfies the required signed-range condition, then from any initial memory, the compiled program executes for $\mathrm{dispPos}(P,d)+\mathrm{frameSize}(P)+9$ steps from position $0$ to $\mathrm{mainPos}$, with the initialized memory specified by $\mathrm{startMem}$.

**Proof.** The compiled program begins with the three straight instructions of `headStraight`, which establish the words for $1$, $0$, and $-1$ (`Light.Compiler.effects_headStraight_consts`). The code layout identifies this prefix (`Light.Compiler.codeAt_headCode`), and straight-code execution runs it in three steps (`WordRAM.steps_straight`). The next instruction branches on the negative register to the startup code; the register contains the encoding of $-1$, so the one-step jump rule (`Light.Compiler.steps_jump`) sends execution to the startup section.

The startup section is itself straight (`Light.Compiler.straight_startStraight`) and occurs at the position specified by `Light.Compiler.codeAt_startCode`. Its effects initialize the pool and frame. In particular, the negative-register value is preserved: `Light.Compiler.startMem_eq` expresses the initialized memory as the frame-code effects applied to the pool initialization, `Light.Compiler.poolMem_consts` supplies the negative value before frame initialization, and `Light.Compiler.agreeOutside_frameCode` shows that the frame code does not change that cell. The bound `Light.Compiler.three_le_frameSize` supplies the frame-size condition needed for this preservation. Thus the final branch again sees the encoding of $-1$ and jumps back to `mainPos` by `Light.Compiler.steps_jump`.

Composing these runs with `WordRAM.Steps.trans` gives the execution; `Light.Compiler.length_startStraight` and the three-instruction head length show that the total is the stated count. The proof's final count adjustment is just the corresponding arithmetic equality (`WordRAM.Steps.cast_count`).

**Key facts.** `Light.Compiler.codeAt_headCode`, `Light.Compiler.codeAt_startCode`, `Light.Compiler.effects_headStraight_consts`, `Light.Compiler.startMem_eq`, `Light.Compiler.poolMem_consts`, `Light.Compiler.agreeOutside_frameCode`, `Light.Compiler.three_le_frameSize`, `WordRAM.AgreeOutside.cell`, `WordRAM.steps_straight`, `Light.Compiler.straight_headStraight`, `Light.Compiler.steps_jump`, `Light.Compiler.straight_startStraight`, `WordRAM.Steps.trans`, `Light.Compiler.length_startStraight`, `WordRAM.Steps.cast_count`.
