<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_anchor_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return from an anchor state

**Claim.** Under the stated first-visit and release hypotheses, after $t+1$ host steps the host is in the call configuration built from the body's time-$t$ configuration halted, with release false and flag false, while preserving the word, fuel configuration, and other supplied data.

**Proof.** Since the body run is still live at time $t$, the live-prefix fact (`f2_loop_live_prefix`) shows it was live at every earlier time, including time zero. The body-run simulation (`f2_loopBody_run`) then says that through time $t$ the padded body follows the original body run; its first-visit hypothesis prevents the augmented machine from stopping early at the anchor. At time $t$, the body is at the anchor by assumption. The special stopping transition (`f2_loopBody_stop`) takes one further step, halts the body, and sets its flag to false. The padded body source simulates this run without changing the auxiliary tapes (`f2_loopBodySource_run`). Finally, the host captures the live source run through time $t$ by `f2_loopHost_body_capture`; applying this capture correspondence for the first $t$ steps and then the stopping step yields the asserted call configuration after $t+1$ steps. The hypotheses at time zero ensure the release bit is false when that initial state must be inspected.

**Key facts.** `Turing.FinTM.f2_loop_live_prefix`, `Turing.FinTM.f2_loopBody_run`, `Turing.FinTM.f2_loopBody_stop`, `Turing.FinTM.f2_loopBodySource_run`, `Turing.FinTM.f2_loopHost_body_capture`.
