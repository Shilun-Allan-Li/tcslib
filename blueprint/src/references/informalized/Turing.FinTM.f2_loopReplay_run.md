<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopReplay_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay Run on a Boolean Word

**Claim.** For any prefix $u$, suffix $v$, and output word $o$, the replay machine started with tape $uv$, head at $|u|$, and active state reaches after $|v|+1$ steps a halted configuration with the same tape, head at $|uv|$, and output $ov$.

**Proof.** Induct on the suffix $v$, keeping the prefix and output arbitrary. If $v$ is empty, the one-step replay rule halts at the current head position, retains the prefix as the tape, and leaves the output unchanged (`f2_loopReplay_step`); the successor-run identity turns this transition into the claimed one-step run (`runFrom_succ_eq_step`). If $v=b::v'$, the same step rule emits $b$, advances the head by one, and leaves the tape as $u(b::v')$. The remaining run is the induction hypothesis applied with prefix $ub$ and output $ob$. Its length is $|v'|+1$, so together with the first transition the length is $|v|+1$; its final head position, tape, and output are respectively $|uv|$, $uv$, and $ov$.

**Key facts.** `Turing.FinTM.f2_loopReplay_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
