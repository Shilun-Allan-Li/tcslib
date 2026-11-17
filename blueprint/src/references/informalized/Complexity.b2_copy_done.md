<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_copy_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary turn after copying

**Claim.** From the specified loader state with the input head at the right boundary and the assembly buffer holding $x$ with its head at $|x|$, one host step under either choice bit reaches loader state $1$, moves the input head to $|x|$, and leaves the buffer, its head, the other tapes, and the output as stated.

**Proof.** At position $|x|+1$ the input head reads the right boundary blank; this follows from the boundary case of the input-symbol characterization (`inputSymbol_at`). In loader state $0$, the host's transition on a blank moves the input head one place left and changes the control state to loader state $1$, without writing on any work tape or producing output. The control-action application rule (`controlAction_apply`) records these effects while preserving the remaining configuration data. The left-move position formula (`moveInputPos_neg_val`) gives the new position $(|x|+1)-1=|x|$, so the resulting configuration is exactly the one claimed.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`.
