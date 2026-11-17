<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.apply_regAct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Action

**Claim.** Applying the specified action to the configuration with state $s$, register $r$'s tape $f$, and head position $p$ gives state $s'$, the tape prescribed by the write instruction, and head position $p+mv$ at $r$; all other configuration data are unchanged.

**Proof.** The action sets the state to $s'$ and has zero input movement, so the input position stays fixed (`Turing.moveInputPos_zero`). At register $r$, an absent write leaves $f$ unchanged, while a present write updates $f$ at $p$ with the specified optional symbol. Every other register has no write and zero movement. Hence all other tapes and head positions are unchanged; the head at $r$ moves from $p$ to $p+mv$. The action emits no output, so the output is preserved.

**Key facts.** `Turing.moveInputPos_zero`.
