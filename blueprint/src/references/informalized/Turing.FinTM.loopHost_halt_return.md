<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_halt_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Genuine Halt Return

**Claim.** Suppose the body machine stays live through every time $u<t$, avoids the anchor state at every intermediate positive time, and is halted at time $t>0$. Then the loop host, started in the non-startup call on the initial body configuration with release set and no stop flag, follows the body for $t$ steps and ends in the non-startup call on its time-$t$ configuration, with release clear and stop flag true, retaining the words and fuel configuration.

**Proof.** The hypotheses imply that the initial body configuration is live, and they give the invariant needed to follow the instrumented body. At every time $u<t$, either $u=0$, where the release flag is set, or $u>0$, where the body state is not the anchor. Thus the instrumented body does not halt early: its special stopping condition, reaching the anchor with release clear, never occurs before time $t`.

The host's body-call simulation (`loopHost_body_run`) therefore identifies its first $t$ steps with the corresponding run of the padded body source. The source run is just the instrumented body run with the extra tapes carried along (`loopBodySource_run`). By the body-run invariant (`loopBody_run`), the body component at time $t$ is the original time-$t$ configuration, the release flag is now clear since $t>0$, and the added stop flag is true because the body is halted there. Reassembling the padded configuration yields exactly the claimed non-startup call; the word and fuel tapes are unchanged throughout.

**Key facts.** `Turing.FinTM.loopHost_body_run`, `Turing.FinTM.loopBodySource_run`, `Turing.FinTM.loopBody_run`.
