<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_call_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a Loop-Body Call

**Claim.** Under the stated live-run and anchor-avoidance assumptions, after $t$ steps the host machine is in the encoded call configuration for the body machine after $t$ steps. The release flag is retained exactly at time zero, the additional flag records whether the body has halted, and the word and fuel configuration are unchanged.

**Proof.** Unfold the encoded call and its padded body configuration. The host's body-call simulation lemma (`f2_loopHost_body_capture`) says that, as long as the simulated body-source run has not halted before the endpoint, the host run is exactly the capture of that source run. The source-padding lemma (`f2_loopBodySource_run`) identifies that run with the padded configuration obtained by evolving the constructed loop-body machine while leaving the added word and fuel tapes in place. The loop-body simulation lemma (`f2_loopBody_run`) then identifies its state after $t$ steps: it contains the body's actual configuration at time $t$, retains the original release flag only if $t=0$, and sets the additional flag precisely when that body configuration is halted. Its word and fuel tapes are unchanged by the padding construction. The live-run hypothesis ensures the host-capture lemma's no-early-halt condition, while anchor avoidance prevents the loop-body machine's special anchor transition from intervening during the simulated prefix.

**Key facts.** `Turing.FinTM.f2_loopHost_body_capture`, `Turing.FinTM.f2_loopBodySource_run`, `Turing.FinTM.f2_loopBody_run`.
