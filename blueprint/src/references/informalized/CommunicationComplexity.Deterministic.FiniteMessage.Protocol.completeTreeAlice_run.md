<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the complete Alice-query tree

**Claim.** On inputs $(x,y)$, the complete tree of Alice's $d$ queries evaluates to the same output as the continuation protocol indexed by the pattern of query answers on $x$.

**Proof.** Induct on $d$. At depth zero, the only pattern is the empty one, so the tree is already the corresponding continuation. For the successor step, the root query selects the subtree whose first bit is the answer to the first query on $x$. By the induction hypothesis, that subtree evaluates as its continuation indexed by the answers to the remaining queries. The first answer followed by those remaining answers is exactly the full pattern $i\mapsto \mathrm{query}_i(x)$: a pattern on $\mathrm{Fin}(d+1)$ is determined by its value at the first index and its tail. Hence the two continuation protocols, and therefore their evaluations, agree.
