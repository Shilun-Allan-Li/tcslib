<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessTail_canonical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Access-Tail Result

**Claim.** The access-tail operation on $w_i$ and $w_r$, initialized with Boolean state $e$ and no remembered last bit, returns no value if $w_i$ is noncanonical; otherwise it returns the conjunction of $e$ and the assertion that $w_i=w_r$.

**Proof.** The tail-comparison formula (`accessTail_eq`) says that the operation returns no value exactly when the last bit of $w_i$ is false, and otherwise returns $e$ conjoined with the assertion $w_r=w_i$. With no remembered last bit, this condition is expressed by $w_i.getLast?\ne\mathrm{some}(\mathrm{false})$. If $w_i$ is empty, this condition holds and the defining condition for `Canon` holds vacuously. If $w_i$ is nonempty, its last optional bit is its actual last bit, so the condition says exactly that this bit is true, which is `Canon`. Finally, the equality tests for $w_r=w_i$ and $w_i=w_r$ agree by symmetry. Substituting these equivalences gives the stated formula.

**Key facts.** `Complexity.LogProg.accessTail_eq`.
