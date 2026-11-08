<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_timed_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Branch Initialization

**Claim.** If $D$ computes $[b]$ on $x$ within $T$ steps, then within $2T+5$ steps the timed conditional machine reaches the configuration containing the initial configuration of the branch selected by $b$, together with suitable $D$-block tapes and heads and $b$ stored on the extra tape.

**Proof.** Choose the earliest halting time $t$ of $D$ on $x$. Since it halts by time $T$, minimality gives $t\le T$, and every earlier configuration is live. Let $c$ be the configuration at time $t$. It is halted; its output is $[b]$, because the assumed computation also halts with that output and outputs are unique (`computesInTime_iff`, `ComputesInTime.output_unique`). By the initial-control identity (`f2_timed_control_init`) and the capture lemma (`f2_timed_capture`), the timed machine is at the control configuration associated with $c$ at time $t$. The two-step reading lemma (`f2_timed_read`) then places it in the ready configuration for $b$.

From there, the rewind lemma (`timed_rewind`) scans back along the input and returns the input head to position $1$, then enters the selected branch's initial state. It gives a rewind duration $r\le c$'s input-head position plus $2$. Take $a=t+2+r$ and use the $D$-run's input-head bound (`timed_input_bound`): starting at position $1$, after $t$ steps the head position is at most $1+t$. Hence $a\le t+2+(1+t+2)=2t+5\le 2T+5$. The rewind does not alter the branch tapes or the stored bit, so the resulting configuration has the required form, with the $D$-block contents and head positions taken from $c$. Run concatenation (`runFrom_add`) combines the capture, two reading steps, and rewind into the asserted run at time $a$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.FinTM.f2_timed_control_init`, `Turing.FinTM.f2_timed_capture`, `Turing.FinTM.f2_timed_read`, `Turing.FinTM.timed_rewind`, `Turing.MultiTapeTM.timed_input_bound`, `Turing.MultiTapeTM.runFrom_add`.
