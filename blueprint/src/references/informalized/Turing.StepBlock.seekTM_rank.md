<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.seekTM_rank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Search Past a Ranked List

**Claim.** If the list length equals the rank and the summary head scans blank, then starting in the state carrying that rank, the machine reaches done after $1+\operatorname{cost}(A)$ steps. It advances the table head by the encoding length of the list, does not reach done earlier, and preserves the input position, tape contents, output, and all other work-tape heads throughout.

**Proof.** First consider the initial state-carrying transition, whose behavior is given by `seekTM_stateStep`. Since the summary head scans blank, the machine does not enter the branch that begins a new group search. If the rank is zero, the list is empty by the length hypothesis; the transition goes directly to done, and the cost of the empty list is zero. The claims then follow by checking time zero and time one. Otherwise the list is nonempty, and the rank is positive. The same transition decreases the rank by one and enters a request state with the last flag set. The length hypothesis identifies this decremented rank with $|A|-1$. Also, $|A|=r<3^{k+1}$, so the list satisfies the bound required by `seekTM_many`. Apply that result to process the list: because the last flag is true, the request traversal ends in done, advances the table head by the encoding length, and preserves the other stated data without reaching done during that traversal. Prepending the initial state-carrying transition and using the successor-run law (`Turing.MultiTapeTM.runFrom_succ_eq_step`) gives the total time $1+\operatorname{cost}(A)$. At time zero the machine is still in the state carrying the rank; all later times before the endpoint correspond to the nonterminal portion covered by `seekTM_many`. Its frame property, together with the initial transition's unchanged tapes and output, gives preservation throughout.

**Key facts.** `Turing.StepBlock.seekTM_stateStep`, `Turing.StepBlock.seekTM_many`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
