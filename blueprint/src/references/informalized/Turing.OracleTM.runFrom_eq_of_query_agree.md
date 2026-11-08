<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.runFrom_eq_of_query_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on Encountered Queries

**Claim.** If the two oracles give the same membership answer to every query encountered before time $t$ in the run using $O$, then the configurations after $t$ steps using $O$ and $O'$ are equal.

**Proof.** The proof passes through the machine's nondeterministic simulation. Take a length-$t$ sequence of negative answers; with this sequence, its run-with-answers agrees with the original oracle run at each time up to $t$. The hypothesis on encountered queries therefore supplies the matching-answer condition required by the simulation result, which says that the two answer-guided runs agree at every prefix. In particular they agree at the full length-$t$ prefix. Finally, the lemma identifying a run with $t$ repeated negative answers with the ordinary oracle run converts both sides back to the original runs, proving the desired equality.

**Key facts.** `Turing.OracleTM.runWith_take_eq_of_agree`, `Turing.OracleTM.runWith_take_replicate`.
