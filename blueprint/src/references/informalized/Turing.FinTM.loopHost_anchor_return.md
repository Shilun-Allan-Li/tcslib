<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_anchor_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capturing an Anchor Return

**Claim.** Under the stated first-return and release hypotheses, after $t+1$ steps the loop host run from the image of the padded body configuration equals the image of the padded body run at time $t$, with the body halted, release false, and flag false.

**Proof.** First, since the body run is still in the anchor state at time $t$, the body cannot have halted by then: state-never-becomes-live-again for a run (`runFrom_state_ne_none_of_le`) gives that it is live at every time up to $t$. In particular the initial configuration is live. Apply the live body-run simulation (`loopBody_run`) through time $t$. The hypotheses excluding earlier anchor visits ensure that the stopped-body machine has not stopped prematurely; the release condition handles the possible time-zero exception. At time $t$, the simulated configuration is the body configuration with its release bit false. One further step triggers the anchor-stop transition, which halts the extended body and sets the flag false (`loopBody_stop`). Finally, the padded body source simulates this run (`loopBodySource_run`), and the host simulates the padded body source for these steps (`loopHost_body_run`); the required live-prefix condition follows from the same fact that the body run remains live through time $t$. Combining these equalities gives the asserted host configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`, `Turing.FinTM.loopBody_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.loopBody_stop`, `Turing.FinTM.loopBodySource_run`, `Turing.FinTM.loopHost_body_run`.
