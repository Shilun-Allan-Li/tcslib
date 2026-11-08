<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_fuel_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Setup

**Claim.** Starting in controller phase $0$ with blank counter tape, payload tape storing $w$, counter head at $0$, payload head at $|w|$, and output $o$, the host reaches phase $4$ after $3|w|+4$ steps. The counter then stores $w$, the payload is blank, both heads are at $0$, and the rest of the frame data and output are unchanged, also when $w$ is empty.

**Proof.** First, one phase-$0$ transition moves the payload head left and enters phase $1$, placing it at $|w|-1$. The frame effect of this control action is given by `loopControl_apply`. Split the remaining run into three blocks of $|w|+1$ steps. In the first block, the host scans the payload left and reaches phase $2$; this is the payload-scan result `loopHost_payload_scan`. In the second block it copies the payload to the counter, erasing the payload as it goes; the empty-prefix instance of `loopHost_fuel_copy` applies, and `loopCopy_initial` identifies the initially scanned tape with the buffer storing $w$. In the third block it rewinds the counter and payload heads to zero and enters phase $4$; this is `loopHost_fuel_return` with $j=|w|$. The run-addition law `runFrom_add` composes these consecutive blocks, and `runFrom_succ_eq_step` accounts for the initial transition. Their lengths sum to $1+3(|w|+1)=3|w|+4$, and the stated frame is the result.

**Key facts.** `Turing.FinTM.loopControl_apply`, `Turing.FinTM.loopHost_payload_scan`, `Turing.FinTM.loopHost_fuel_copy`, `Turing.FinTM.loopCopy_initial`, `Turing.FinTM.loopHost_fuel_return`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
