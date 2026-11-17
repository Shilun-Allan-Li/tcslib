<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.lenParse_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Aligned Parser Block

**Claim.** If $x=pbd s$, then from the parse configuration at position $|p|$ with counter $r$, after two steps the checker is at position $|p|+2$ in the parse state when $b=d$; if $b=1,d=0$, it halts at position $|p|+1$ with output $[0]$; and if $b=0,d=1$, it enters the suffix-comparison state at position $|p|+2$.

**Proof.** The first parser step reads $b$, moves right, and records that bit in the state, leaving the counter unchanged (`lenParse_first`). At the resulting position the next input symbol is $d$, by the decomposition $x=pbd s$; the checker reads it using the input-symbol description (`lenCfg_read`). The transition rule now compares the recorded bit with $d$. If they agree, it advances to the next parse position and clears the recorded bit. If the recorded bit is $1$ and $d=0$, it halts and outputs $0$ without advancing. If the recorded bit is $0$ and $d=1$, it advances and switches to suffix comparison. The positive input-head movement advances by one here because the head is not at the right boundary (`moveInputPos_pos_of_ne_right`). The resulting one-step configuration descriptions, including counter and output, follow from the action-application calculation (`lenAction_apply`).

**Key facts.** `Turing.FinTM.lenParse_first`, `Turing.FinTM.lenCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.lenAction_apply`.
