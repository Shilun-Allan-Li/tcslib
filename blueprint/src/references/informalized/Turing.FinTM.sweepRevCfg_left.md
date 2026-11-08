<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepRevCfg_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep at the Frontier

**Claim.** Applying the action that writes $b$, moves the work head left, and enters state $q'$ to the backward-sweep configuration with right stack $a::r$ produces the backward-sweep configuration with state $q'$, the same input-head position and output, frontier $z-1$, left stack $b::l$, and right stack $r$.

**Proof.** Compare the configuration fields. The action sets the state to $q'$, leaves the input-head position fixed because a zero input movement preserves it (the identity movement fact, `Turing.moveInputPos_zero`), and emits no output. Its work-head position changes from $z$ to $z-1$. For the tape contents, the action updates the old tape at position $z$ with value $b$. The zipper identity that updating the frontier cell of a tape represented by $(z,l,a::r)$ gives the representation $(z+1,b::l,r)$ (`Turing.FinTM.sweepTape_right`) applies to the reflected tape coordinate $-w$. Since $-(z-1)=-z+1$, this is exactly the tape represented by the new backward-sweep configuration at coordinate $w$. Thus all fields agree.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.sweepTape_right`.
