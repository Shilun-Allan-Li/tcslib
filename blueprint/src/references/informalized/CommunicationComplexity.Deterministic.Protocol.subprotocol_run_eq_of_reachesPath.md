<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.subprotocol_run_eq_of_reachesPath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Along a Subprotocol Path

**Claim.** If $(x,y)$ satisfies the branch choices along a path from $p$ down to $s$, then $p$ and $s$ return the same output on $(x,y)$.

**Proof.** Proceed by induction on the path. For a path of length zero, $p=s$, so the outputs agree. If the first step is an Alice node whose selected branch is false, reachability ensures $f(x)=\mathrm{false}$. Thus running the parent protocol follows that branch, and the induction hypothesis applies to the remaining path, with the inherited reachability conditions. The true branch is identical, using $f(x)=\mathrm{true}$. If the first step is a Bob node, reachability instead gives the corresponding value of $f(y)$, so the parent follows the indicated branch; applying the induction hypothesis to the rest of the path proves agreement in either branch.
