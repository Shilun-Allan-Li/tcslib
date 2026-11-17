<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_halt_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return After a Body Halts

**Claim.** If the body machine remains live before time $t$, avoids anchor state $a$ at strictly intermediate positive times, and halts at time $t>0$, then the loop host’s call configuration after $t$ steps represents the body run at time $t$, with release unset and the flag bit set; the other call data are retained.

**Proof.** The initial configuration is live, since the hypothesis applies at time zero. To use the body-machine simulation, verify its anchor-avoidance condition at each time $u<t$: at $u=0$ the release bit is true, so the guarded anchor halt does not trigger; for $u>0$, the assumed avoidance of $a$ applies. The simulation lemma for the augmented body machine (`f2_loopBody_run`) now identifies its run through time $t$ with the original body run, with release cleared after the first step and the flag set precisely when the body halts. The padded-source lemma (`f2_loopBodySource_run`) transports this run to the host’s body tapes while leaving the added tapes fixed. Finally, the host body-capture lemma (`f2_loopHost_body_capture`) says that, as long as the simulated body source is not halted before time $t$, the host run agrees with capturing that source configuration. The live-run hypothesis supplies this condition; at time $t$, the assumed halt and positivity of $t$ give the stated call state and flag, while the captured word, fuel tapes, input, and other call data remain as specified.

**Key facts.** `Turing.FinTM.f2_loopBodySource_run`, `Turing.FinTM.f2_loopBody_run`, `Turing.FinTM.f2_loopHost_body_capture`.
