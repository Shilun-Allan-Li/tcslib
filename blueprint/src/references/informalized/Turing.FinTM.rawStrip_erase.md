<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.rawStrip_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the final bit

**Claim.** From state $1$ with $w$ followed by $b$ on the work tape and the head at its final position, one step erases $b$, leaves $w$, and moves the head to $|w|-1$. The input-head position and empty output are unchanged, and the new state records whether $b$ was true.

**Proof.** The length of $w$ followed by one bit is $|w|+1$, so the work head starts at coordinate $|w|$. At that coordinate the tape contains exactly the appended bit. The transition in state $1$ writes nothing when the bit is false and erases the scanned cell when it is true; in either case the resulting tape agrees with $w$. This is the tape update expressed by the catalog erasure fact (`catalogBuffer_erase`). The transition moves the work head one place left, to $|w|-1$, and does not move the input head; zero input movement leaves its position fixed (`moveInputPos_zero`). It emits no output and chooses state $1$ for false and state $2$ for true. Unfolding one machine step therefore gives precisely the stated configuration.

**Key facts.** `Turing.FinTM.catalogBuffer_erase`, `Turing.moveInputPos_zero`.
