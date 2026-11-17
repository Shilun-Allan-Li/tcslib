<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeStore_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the stack assignment

**Claim.** For every stack word $xs$ and index $i\in\{0,1,2,3\}$, evaluating the assignment with $xs$ on the main stack and the other stacks empty at the stack named by $i$ gives $xs$ when $i=0$, and the empty word otherwise.

**Proof.** If $i=0$, the stack key is the main stack, so the assignment evaluates to $xs$ and the conditional also selects $xs$. If $i\ne0$, the key cannot be the main stack: the key-to-index identity (\texttt{bridgeIndex_key}) would otherwise imply $i=0$. Thus the assignment evaluates to the empty word. In this case the conditional also selects the empty word, and the result follows by checking the four stack constructors.

**Key facts.** `Turing.bridgeIndex_key`.
