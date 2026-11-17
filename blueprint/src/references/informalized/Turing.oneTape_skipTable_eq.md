<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.oneTape_skipTable_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of one-tape table skippers

**Claim.** For every natural number $n$ and binary word $x$, the one-tape-format table skipper with bound $n$ returns the same result as the general table skipper with one work tape and bound $n$.

**Proof.** The one-tape action skipper agrees pointwise with the general action skipper specialized to one work tape (Turing.codeSkipAction_eq_codeSkipActionK), hence the two functions are equal. The one-tape table skipper applies the action skipper three times for the three input-symbol cases, then repeats this table block over the $n+1$ states. Replacing each action-skipper occurrence by its equal general form yields exactly the defining nested repetitions of the general one-tape table skipper. Therefore their results on $x$ agree.

**Key facts.** `Turing.codeSkipAction_eq_codeSkipActionK`.
