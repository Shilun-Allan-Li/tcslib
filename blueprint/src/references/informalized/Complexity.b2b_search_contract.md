<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_search_contract -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Search for Fixed-Length Extensions

**Claim.** The specified search machine halts on every Boolean input $x$ with the indicator of whether some word $u$ of length $Q$ satisfies $x++u\in V$. Throughout the run, every work-tape head remains within distance $|x|+Q+c_V((|x|+Q)^e+1)+c_I+1$ of the origin.

**Proof.** Let $d=2^Q-1$. The machine interprets its $Q$-bit word as a counter and tests the length-$Q$ words in their binary enumeration. By the enumeration facts, every word has length $Q$ (`Complexity.Meyer.length_enumWord`), the counter value of the word at index $r$ is $r$ (`Complexity.Meyer.ctrVal_enumWord`), and incrementing the word at any index below $d$ produces the word at index $r+1$ (`Complexity.Meyer.incFixed_enumWord`). Starting from the all-false word, the certificate counter orbit therefore reaches the enumerated word at each successive index (`Complexity.b2b_certificate_orbit`).

For each index $r<d$, one body round tests whether $x$ concatenated with the word at index $r$ belongs to $V$. The clean simulation hypothesis supplies the correct membership bit for that concatenation; the identity machine preserves the input and uses at most $c_I$ space. The round-run result packages these operations: a negative test clears the temporary buffer and advances the counter, while a positive test exits with the positive verdict; it also bounds every work-head position during the round by $W=|x|+Q+c_V((|x|+Q)^e+1)+c_I+1$ (`Complexity.b2b_round_run`).

If some extension is in $V$, choose the least successful index. All earlier tests are negative, so the counter-loop orbit follows the enumerated words up to that index; the positive test then sends the loop to its escape state. The counter-loop escape theorem combines these rounds, and the host-phase run theorem carries that execution into the answer phase (`Turing.counterLoopTM_run_escape`, `Turing.phaseHostTM_run`). The answer routine emits the positive indicator (`Complexity.b2b_finish_answer`). The output thus records existence of an extension, and the round and loop bounds give the asserted head bound through the final answer steps.

If no extension is in $V$, every test before index $d$ is negative. The counter-loop completion theorem runs through all $d+1$ candidates and reaches the ordinary exit. Every length-$Q$ word occurs among these candidates, by the verification equivalence (`Complexity.b2b_verifies_iff`), so the last candidate is negative as well. The final-test theorem then halts with the negative indicator and maintains the same work-head bound (`Turing.counterLoopTM_run_done`, `Complexity.b2b_finish_last`). In both cases, the machine’s initial setup is the prescribed counter-loop configuration, and the run-composition law accounts for adjoining the final phase to the search (`Turing.MultiTapeTM.runFrom_add`).

**Key facts.** `Complexity.Meyer.length_enumWord`, `Complexity.Meyer.incFixed_enumWord`, `Complexity.b2b_certificate_orbit`, `Complexity.b2b_round_run`, `Turing.counterLoopTM_run_escape`, `Turing.counterLoopTM_run_done`, `Complexity.b2b_verifies_iff`, `Turing.phaseHostTM_run`, `Complexity.b2b_finish_answer`, `Complexity.b2b_finish_last`, `Turing.MultiTapeTM.runFrom_add`.
