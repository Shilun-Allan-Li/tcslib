<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.actionBitsK_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Length Action Prefix

**Claim.** The action-bit encoding of a $k$-tape action is a Boolean list of length $4k+4$, followed by the encoding of its optional successor state.

**Proof.** Separate the action encoding into its prefix—input movement, the write-and-movement data for each of the $k$ work tapes, and output—and its successor-state encoding. Each movement, write field, and output field contributes two bits. Thus the prefix has length $2+4k+2=4k+4$. Index this prefix by the finite set of that size; its entries form a Boolean-valued function, and its list of values is the original prefix. Appending the unchanged successor-state encoding gives the claimed decomposition.
