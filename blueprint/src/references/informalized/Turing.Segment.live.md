<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extension of a live segment

**Claim.** If a segment avoids $F$ before its endpoint and its endpoint is not halted, then it also avoids $F\cup\{\text{halt state}\}$ before the endpoint, while retaining the same endpoint and position condition.

**Proof.** The endpoint equation and the condition on work-tape head positions are unchanged. Consider any time $u<t$. To show the state then lies outside $F\cup\{\text{halt state}\}$, first note that it lies outside $F$ by the original segment. It is also not the halting state: the endpoint is not halted, and a run whose state at time $t$ is nonhalting must have been nonhalting at every earlier time $u\le t$ (the persistence of nonhalting states, $\texttt{Turing.MultiTapeTM.runFrom_state_ne_none_of_le}$). Thus the state lies outside both parts of the union.

**Key facts.** `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`.
