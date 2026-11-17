<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.hlQuery_mem_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Membership and Halting

**Claim.** For every natural number $j$, the word consisting of $\operatorname{haltPrefix}(j)$ ones, followed by a zero and then $4^{j+1}$ ones, belongs to the language exactly when the computation indexed by $j$ halts.

**Proof.** The query-parameter identities (`Randomized.hlN_hlQuery`) give head-output length $\operatorname{haltPrefix}(j)$ and logarithmic parameter $j+1$. Substitute these into the language-membership conditions. The parameter condition holds since $1\le j+1$, and $(j+1)-1=j$, so the required head length and halting condition become exactly the defining prefix and the assertion that the computation indexed by $j$ halts. Thus membership is equivalent to that halting assertion.

**Key facts.** `Randomized.hlN_hlQuery`.
