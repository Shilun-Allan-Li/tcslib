<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.erasePath_run_outside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasure Preserves Runs Outside the Path

**Claim.** If $(x,y)$ does not reach the subprotocol $s$ along the path from $s$ to $p$, then erasing that path leaves the run on $(x,y)$ unchanged.

**Proof.** Induct on the path from $s$ to $p$. In the reflexive case every input reaches the path, so the hypothesis is impossible. At each non-reflexive step, the path enters one branch of the root; choose Alice's bit $f(x)$ or Bob's bit $f(y)$ as the branch selected by the input. The one-branch preservation result (`erasePath_run_outside_branch`) compares the erased and original protocols at that node. If the input selects the branch containing the path, the assumption that it does not reach $s$ implies that it does not reach the subpath below, and the induction hypothesis says erasure preserves its run there. If it selects the other branch, that branch is untouched. Thus in either case the output is preserved.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.erasePath_run_outside_branch`.
