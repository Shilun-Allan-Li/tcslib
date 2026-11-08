<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_input_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Head Rewind

**Claim.** If the loop host is in control phase $4$, then for some $t\leq c$'s input-head position plus $2$, it reaches the startup body-call state with the body in its initial state and input-head position $1$, leaving all other configuration data unchanged.

**Proof.** Apply the bounded rewind principle to the host machine, taking phase $4$ as the starting state, phase $5$ as the scanning state, and the startup body-call state as the destination. The principle applies because every transition from phase $4$ moves the input head left and enters phase $5$, while phase $5$ keeps moving left whenever it reads an input symbol and moves right into the destination when it reaches the left boundary. In these phases the control action is exactly the generic input-rewind action (`f2_loopControl_idle`), so the counter, payload, flag, output, and other tapes are unchanged. The bounded rewind principle then gives the destination configuration with input position $1$ in at most the starting position plus $2$ steps.

**Key facts.** `Turing.FinTM.f2_loopControl_idle`, `Turing.FinTM.f2_loop_rewind_bounded`.
