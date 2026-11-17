<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_read_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Head Positions After Control Steps

**Claim.** Under the stated hypotheses on a halted configuration $c$ whose output is $[b]$, after each $u\le2$ steps of the timed conditional machine from its timed control configuration, the work heads have the original positions of $c$ in the first block, zero positions in the next block, and a final position $z$ with $0\le z\le1$.

**Proof.** Because $u\le2$, it suffices to consider $u=0,1,2$. At $u=0$, the control configuration has its original head positions in the first block, zeros in the second, and final head position equal to the output length. Since the output is the one-bit word $[b]$, this length is $1$; this is precisely the control-head identity (`Turing.FinTM.f2_control_heads`), with $z=1$. At $u=1$, the halted simulated configuration is captured and the control transition moves the final head left, so its position is $0$. The other two blocks retain their stated positions, as follows by inspecting that transition and the same head-position identity. At $u=2$, the timed-read computation (`Turing.FinTM.f2_timed_read`) identifies the resulting configuration with the ready configuration, whose head positions have the required block form with final position $0$. Thus the respective choices $z=1,0,0$ all lie in the required interval.

**Key facts.** `Turing.FinTM.f2_control_heads`, `Turing.FinTM.f2_timed_read`.
