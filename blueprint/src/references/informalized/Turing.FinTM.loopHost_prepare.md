<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation reaches startup

**Claim.** For every input, the fuel machine has a halted configuration with the required binary output, reached within its time bound, and the loop host reaches the prepared startup configuration built from it within the stated bound.

**Proof.** Fix an input $x$. The fuel-machine hypothesis supplies a time $T(|x|)$ at which the fuel machine has halted, has output the binary digits of $R(|x|)$, and has some space usage. The first-halt principle (`loop_first_halt`) replaces this time by the first halting time $u$: it is positive, at most $T(|x|)$, the machine is live at every earlier time, and its configuration at $u$ agrees with the configuration at the original time. Let $c$ be the fuel configuration at time $u$. It is halted and has the required output.

The loop host first simulates the fuel machine while capturing its configuration. The fuel-run correspondence (`loopFuel_run`) identifies the padded fuel simulation with the original run, and the capture lemma (`loopHost_fuel_capture`) applies because the fuel run is live before $u$. Thus after $u$ steps the host is in the captured configuration corresponding to $c$.

Next, the host transfers the captured output to its counter tape. The setup lemma (`loopHost_fuel_setup`) says this takes $3|c.output|+4$ steps and leaves the host in phase four with the counter cleared and the output word on the payload tape. The output-width bound (`loop_fuel_width`) gives $|c.output|\le T(|x|)$. The input-head displacement bound (`timed_input_bound`) gives $c.inputPos\le 1+u$; the rewind procedure (`loopHost_input_rewind`) then returns the input head to its initial position and enters the released startup call in at most $c.inputPos+2$ further steps. Combining these run segments with the run-addition law (`runFrom_add`) yields the asserted equality with the prepared configuration. Finally, $u\le T(|x|)$ and $|c.output|\le T(|x|)$ give the total bound $u+3|c.output|+4+v\le 5T(|x|)+7$.

**Key facts.** `Turing.FinTM.loop_first_halt`, `Turing.FinTM.loopFuel_init`, `Turing.FinTM.loopFuel_run`, `Turing.FinTM.loopHost_init`, `Turing.FinTM.loopHost_fuel_capture`, `Turing.FinTM.loopFuelCaptured_frame`, `Turing.FinTM.loopHost_fuel_setup`, `Turing.FinTM.loopHost_input_rewind`, `Turing.FinTM.loop_fuel_width`, `Turing.MultiTapeTM.timed_input_bound`, `Turing.MultiTapeTM.runFrom_add`.
