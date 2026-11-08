<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_lenParse_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing One Aligned Bit Pair

**Claim.** After two steps from the parser state at the beginning of the pair $b,d$, equal bits leave the machine in the pair-reading state at the position after the pair; unequal bits with $b=1$ halt after the first bit and output $[0]$; unequal bits with $b=0$ enter state $3$ after the pair.

**Proof.** The first step reads $b$, records it in the parser state, and advances one position (`f2_lenParse_first`). The second step therefore reads $d$. The input-symbol formula for the length-counting configuration identifies this scanned symbol as $d$ (`f2_lenCfg_read`). The transition rule now compares the recorded bit $b$ with $d$: if they agree, it advances and returns to the pair-reading state; if $b=1$ and $d=0$, it emits false and halts without advancing; if $b=0$ and $d=1$, it advances into state $3$. The two-step configuration statement follows from the one-action effect on position, state, and output (`f2_lenAction_apply`). In the advancing cases, a positive input move increases the shifted head position by one because the current position is not the right boundary (`moveInputPos_pos_of_ne_right`); in the halting case, zero movement leaves it fixed (`moveInputPos_zero`).

**Key facts.** `Turing.FinTM.f2_lenParse_first`, `Turing.FinTM.f2_lenCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_zero`, `Turing.FinTM.f2_lenAction_apply`.
