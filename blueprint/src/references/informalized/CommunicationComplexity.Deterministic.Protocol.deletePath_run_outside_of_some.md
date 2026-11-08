<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.deletePath_run_outside_of_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deletion Preserves Unreached Runs

**Claim.** If deleting the path from $p$ to $s$ yields a protocol $q$, then every input pair that does not reach $s$ along that path has the same output under $q$ and $p$.

**Proof.** Induct on the path from $s$ to $p$, generalizing the deleted protocol $q$. For the reflexive path, deletion returns nothing, contradicting the hypothesis that it returns a protocol. At each other step, the path enters one specified branch of the root, either Alice's false or true branch, or Bob's false or true branch. Apply the one-branch preservation result (`deletePath_run_outside_branch`), taking the constructor to be the corresponding root protocol and its selected bit to be Alice's value $f(x)$ or Bob's value $f(y)$. If the input follows the path at this root, failure to reach $s$ means it fails to reach the subpath below, so the induction hypothesis applies. The branch result then gives equality of the two runs.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.deletePath_run_outside_branch`.
