<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.Goes.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Counter-Program Runs

**Claim.** Two runs with matching intermediate label, registers, and input position compose into a run reaching the second endpoint, appending the concatenation of their output extensions within the sum of their step bounds.

**Proof.** Fix an initial output word $o$. The first hypothesis supplies a time $t\le b$ reaching the intermediate configuration with output $o$ followed by $e$. Apply the second hypothesis to that output word; it supplies a time $t'\le b'$ reaching the final configuration and appending $e'$. By the run concatenation identity (`run_add`), these runs combine into a run of length $t+t'$. This length is at most $b+b'$. The final output is $(o\mathbin{++}e)\mathbin{++}e'$, which by associativity equals $o\mathbin{++}(e\mathbin{++}e')$.

**Key facts.** `Complexity.CounterProg.run_add`.
