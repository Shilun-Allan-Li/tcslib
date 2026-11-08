<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.run_append_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution After Shifting Gate References

**Claim.** Executing a gate list followed by a second list whose internal references have been shifted by the length of the first produces the execution values of the first list followed by those of the second list.

**Proof.** First establish a stronger statement for any already-computed value list $v$ and any auxiliary list $w$: folding through the shifted gates of $h$, starting from $v$ followed by $w$, has the same effect as keeping $v$ fixed and folding through the unshifted gates of $h$ starting from $w$. Induct over $h$. At each gate, shifting its references by the length of $v$ makes them address the corresponding positions in the part after $v$; the evaluation identity for shifted gates gives the same new value (`Randomized.AlgGate.eval_shift`). The empty list is immediate. Apply this statement with $v$ the execution of the first list and $w$ empty. Execution length equals gate-list length (`Randomized.AlgCircuit.length_run`), so the shift used is exactly the required offset, and folding over the concatenated gate lists gives the claimed concatenation of execution values.

**Key facts.** `Randomized.AlgGate.eval_shift`, `Randomized.AlgCircuit.length_run`.
