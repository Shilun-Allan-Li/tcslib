<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Implies Membership

**Claim.** If $N$ decides $L$ under the stated space-bounded halting condition, then acceptance of $x$ within any number of steps implies $x\in L$.

**Proof.** Take the time $T$ supplied by the decision hypothesis for $x$, including its halting-on-every-branch property and the equivalence between membership and acceptance at time $T$. Let $x$ have an accepting run of length $t$. If $t\le T$, extend that accepting run to length $T$ using monotonicity of acceptance (\texttt{AcceptsWithin.mono}); the correctness equivalence at $T$ then gives $x\in L$. If $t>T$, write the accepting choice word as its prefix of length $T$ followed by the remaining choices. The run on that prefix halts by the hypothesis. A halted configuration is unchanged by further choices (\texttt{runWith_of_halt}); together with the decomposition law for runs (\texttt{runWith_append}), this shows the full run has the same configuration, and thus the same output, as the prefix run. The prefix therefore witnesses acceptance at time $T$, so the correctness equivalence again gives $x\in L$.

**Key facts.** `Turing.FinNDTM.AcceptsWithin.mono`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
