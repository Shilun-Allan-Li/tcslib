<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One round of the loop host

**Claim.** Under the anchor-avoidance hypothesis, a round simulating the body either accepts and halts with the mode-dependent accepted output, returns to the anchor and debits the counter, or underflows and halts with the mode-dependent rejecting output, within the stated time bound.

**Proof.** Let the body start in the clean configuration with state $a$ and tape-zero word $s$. First suppose the run is accepted. The first-halt principle (`loop_first_halt`) selects its first halting time $u\le t$; the run is live before $u$ and, by the anchor-avoidance hypothesis, does not revisit $a$ at intermediate positive times. The halt-return lemma (`loopHost_halt_return`) therefore carries the host through these $u$ simulated steps and places it in the accepted call. The acceptance routine (`loopHost_accept`) then halts the host, outputting the body's output in find mode and the one-bit word true otherwise. Its extra time is at most $2|c.output|+3$, and the output-length bound (`loop_output_length_le`) gives $|c.output|\le u$. Concatenating the two runs by `runFrom_add`, and using that the body's output at $u$ is the specified payload, gives a total at most $u+2u+3\le 3t+2|w|+5$.

Now suppose the body does not accept. The endpoint hypothesis says it returns exactly to the clean configuration with state $a$ and tape-zero word $s'$. The anchor-return lemma (`loopHost_anchor_return`), using the hypothesis that there was no earlier positive-time visit to $a$, carries the host through the body run and reaches the rejecting call with release cleared and the stop flag false. Apply the debit-or-halt result (`loopHost_reject`) to that call. If decrementing $w$ succeeds, it reaches the released call on the returned body configuration with counter `loopDebit`$(w)$. If decrementing fails, it halts with the specified rejecting output. The return segment takes $t+1$ steps and the debit-or-halt segment takes at most $2|w|+4$, so the total is at most $t+1+2|w|+4\le 3t+2|w|+5$, since $t>0$. In both cases, the run-addition law combines the segment equalities into the asserted run.

**Key facts.** `Turing.FinTM.loop_first_halt`, `Turing.FinTM.loopHost_halt_return`, `Turing.FinTM.loopHost_accept`, `Turing.FinTM.loop_output_length_le`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.loopHost_anchor_return`, `Turing.FinTM.loopHost_reject`.
