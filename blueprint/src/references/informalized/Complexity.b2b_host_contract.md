<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_host_contract -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Space Host Computation

**Claim.** Under the verifier, identity-machine, and witness-generator hypotheses, the host halts with the indicator of whether the input has a witness of the prescribed length whose concatenation with it belongs to $V$, and its space use is bounded by the stated expression.

**Proof.** Set $Q=C(|x|+1)^c$, the generated witness length, and let $W$ denote the quantity inside the outer factor $2$ in the asserted bound. First, the setup result (`b2b_setup_run`) gives a time $T$ when the host has generated and prepared the length-$Q$ search, and bounds every head position up to that point by the generator’s space bound plus $Q+1$. Next, the bounded-search result (`b2b_search_contract`) gives a time $t$ from the prepared configuration when the search halts with the desired indicator; throughout this portion it bounds head positions by the input length, $Q$, the verifier’s head bound, the identity machine’s space bound, and a constant overhead. Both bounds are at most $W$ by the definitions and the assumed generator and identity-machine bounds.

Run the host for $T+t$ steps. The run concatenation law (`Turing.MultiTapeTM.runFrom_add`) identifies this run with setup followed by search. It therefore halts with the search result. The equivalence between the machine’s computation predicate and its halting state and output (`Turing.FinTM.computesInTime_iff`) translates this into the claimed computation of the indicator.

For space, fix a work tape. Every cell counted as visited by time $T+t$ is a head position at some time up to $T+t$, so the head bounds place all such positions in the integer interval $[-W,W]$. That interval has $2W+1$ elements. Thus each tape uses at most $2W+1$ cells; summing over the host’s $K+1$ tapes yields $(K+1)(2W+1)$, exactly the stated bound after substituting $Q$ and $W$.

**Key facts.** `Complexity.b2b_setup_run`, `Complexity.b2b_search_contract`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`.
