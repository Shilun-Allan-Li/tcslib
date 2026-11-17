<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.prependTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Emission Time Bound

**Claim.** For every Boolean word $w$, the machine that emits $w$ and then copies its input computes $x\mapsto w\mathbin{++}x$ in $|w|+|x|+1$ steps.

**Proof.** Fix $x$. The computation characterization (`computesInTime_iff`) reduces the claim to showing that the run halts with the stated output. Run first for $|w|$ steps: the prefix-emission phase reaches its configuration with output $w$ and the input head at the start of copying (`catalogPrefixTM_emit`). Then run for another $|x|+1$ steps. The copying phase appends the first $|x|$ input bits to the output (`catalogPrefixTM_copy`), and its final step reads the right end of the input and halts. The accumulated output is $w\mathbin{++}x$, since taking the first $|x|$ bits of $x$ gives $x$ itself. Splitting the total run into these two phases uses the run-addition law (`runFrom_add`); the final transition is expressed by the successor-step law (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.catalogPrefixTM_emit`, `Turing.FinTM.catalogPrefixTM_copy`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
