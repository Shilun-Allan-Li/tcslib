<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.windowRun_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Windowed Run Characterization

**Claim.** Starting from a configuration in the radius-$s$ window, the windowed run returns some configuration along the ordinary run, at a time $r\le N$. The run stays in the window through time $r$, and is nonhalting before then; the reported outcome further determines whether it halted, left the window, or exhausted its clock as stated.

**Proof.** Induct on the clock bound. At bound zero, the windowed run reports exhaustion and returns its initial configuration, so take $r=0$. The run at time zero is in the window by hypothesis, and the remaining assertions follow directly from the zero-time run identity (`runFrom_zero`) and the fact that there are no earlier times. For a positive bound, first consider whether the initial configuration is halted. If so, the windowed run reports halting immediately; take $r=0$. The initial window condition and the halting state give the required claims. If it is not halted, consider whether its next configuration lies in the window. If it does, the windowed run proceeds from that successor with the smaller clock. Apply the induction hypothesis there, obtaining a stopping time $r$ for the shorter run, and use $r+1$ for the original run. The successor-run identity (`runFrom_succ_eq_step`) translates the returned-configuration equality and all window, nonhalting, and outcome conditions back to the original run; the initial configuration supplies the time-zero case of the window and nonhalting conditions. If instead the next configuration is outside the window, the windowed run reports leaving immediately. Take $r=0$: the initial configuration is in the window and nonhalting, while its successor is outside, exactly as required. In each branch the chosen time is within the available clock.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
