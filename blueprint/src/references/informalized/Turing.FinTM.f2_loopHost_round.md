<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Round Behavior

**Claim.** Under the stated first-return exclusion and endpoint assumptions for the body run, the loop host reaches within $3t+2|w|+5$ steps the appropriate accepting halt, successful-debit next call, or rejection halt.

**Proof.** Let the body start in the anchor configuration with tape word $s$. First suppose the run is accepted. The first-halt lemma selects a time $u$ with $0<u\le t$ at which the body halts, with no earlier halted configuration, and whose configuration equals the one at time $t$ (`f2_loop_first_halt`). The exclusion of intermediate visits to the anchor lets the host follow the run and return from this first halt (`f2_loopHost_halt_return`). The acceptance lemma then halts the host with the required output, namely the body output in find mode and the single bit true otherwise (`f2_loopHost_accept`). The body output length is at most $u$ (`f2_loop_output_length_le`), so the combined time is at most $u+(2u+3)\le 3t+3$, within the claimed bound.

Now suppose the run is not accepted. The endpoint is exactly the anchor configuration with tape word $s'$. The anchor-return lemma shows that after $t+1$ host steps the host has this body configuration halted, with the false flag, ready for the debit-or-rejection behavior. Apply the rejection lemma to that configuration: it either reaches the next call with the debited word or halts with the rejection output, using at most $2|w|+4$ more steps. The total is at most $t+1+2|w|+4$, which is at most $3t+2|w|+5$ since $t$ is positive. In the accepted case, the time-composition law for runs combines the host’s return and acceptance phases; in the nonaccepted case it combines the anchor return and debit phase (`runFrom_add`).

**Key facts.** `Turing.FinTM.f2_loop_first_halt`, `Turing.FinTM.f2_loopHost_halt_return`, `Turing.FinTM.f2_loop_output_length_le`, `Turing.FinTM.f2_loopHost_accept`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_loopHost_anchor_return`, `Turing.FinTM.f2_loopHost_reject`.
