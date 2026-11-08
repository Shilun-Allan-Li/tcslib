<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.incrementTM_run_succ_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successful Increment from a Configuration

**Claim.** If incrementing $w$ yields $v$ and the selected tape in an arbitrary run-phase configuration agrees locally with the buffer for $w$, then the machine finishes with true verdict after $2m+2$ steps, where $m$ is the initial run of true bits in $w$, with no earlier done phase and with the stated head bounds.

**Proof.** Decompose $w$ as $p$ true bits followed either by nothing or by a false bit and a remaining tail (`catalog_increment_split`). The increment-value formula (`catalog_increment_value`) and the assumption that the increment equals a word rule out the empty-tail case. Thus $w$ has the form $p$ true bits, then false, then the tail; the formula also identifies $v$ as $p$ false bits, then true, then that tail. This decomposition shows that the initial run of true bits has length $p$. The trace description (`catalog_increment_trace`) now applies with the nonempty tail case. At time $2p+2$ it gives the done phase with true verdict and the tape updated to $v$. At all earlier times it remains in the forward or return part, so it is not done; throughout the run the selected head lies in the claimed interval and the other heads remain fixed. Since $p=m$, these are precisely the stated time and position bounds.

**Key facts.** `Turing.catalog_increment_split`, `Turing.catalog_increment_value`, `Turing.catalog_increment_trace`.
