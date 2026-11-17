<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup reaches the first anchor seam

**Claim.** If the body avoids the anchor before time $t$ and is exactly at the clean anchor configuration with tape-zero word $s$ at time $t$, then after $t+2$ steps the host is in the released startup call on that configuration, with the fuel output as counter and the original fuel configuration retained.

**Proof.** The anchor-return lemma (`loopHost_anchor_return`) applies to the body's run from its initial configuration: the endpoint is in state $a$, and the guard hypothesis excludes every earlier visit. It shows that after $t+1$ steps from the body portion of the prepared startup configuration, the host reaches the corresponding anchor seam. The empty-prefix identification (`loopBodyImage_nil`) identifies the initial padded body configuration with the startup call, and identifies the seam configuration with the call whose release is still clear and whose stop flag is false. The prepared configuration is itself this initial startup call with the fuel output on the counter (`loopReady_call`). One additional host step performs the release transition (`loopHost_release`), changing to the released startup call, clearing the flag, and retaining the fuel residue. The run-at-successor identity (`runFrom_succ_eq_step'`) combines these stages into exactly $t+2$ steps. The counter remains the output of the fuel configuration throughout.

**Key facts.** `Turing.FinTM.loopHost_anchor_return`, `Turing.FinTM.loopBodyImage_nil`, `Turing.FinTM.loopReady_call`, `Turing.FinTM.loopHost_release`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
