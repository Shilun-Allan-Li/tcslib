<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.prefixTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy phase of the prefixing machine

**Claim.** For binary strings $w,x$ and each $i\le |x|$, after $i$ steps from the configuration in the final prefixing state, with input head at position $1$ and output $w$, the machine remains in that state, its input head is at position $i+1$, and its output is $w$ followed by the first $i$ bits of $x$.

**Proof.** Use the characterization of running for $t+1$ steps as one step after running for $t$ steps (`runFrom_succ_eq_step'`) and the supplied copy-phase fact (`prefixTM_copy`). The time is split into the $|w|$ steps that emit the fixed prefix and the $|x|+1$ steps that copy the input. At the end of the emission phase, the machine is in the final prefixing state, the head is at position $1$, and the output is $w$; running the copy-phase fact with $i=|x|$ gives the final state, head position $|x|+1$, and output $w++x$. The output is therefore the requested function value, and the run is halted at that time. The equivalence between computing in time and having the specified final state and output (`computesInTime_iff`) then supplies the required computation claim; the space witness is existential and needs no further specification.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.prefixTM_emit`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.prefixTM_copy`.

**Caveat.** The upstream list does not include the source-used `prefixTM_copy` dependencies needed to establish the detailed copy-phase behavior, but the supplied lemma directly states that behavior.
