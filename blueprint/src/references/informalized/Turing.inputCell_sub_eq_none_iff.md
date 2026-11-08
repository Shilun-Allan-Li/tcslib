<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.inputCell_sub_eq_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When a Shifted Input Cell Is Blank

**Claim.** For $0<\ell\le p\le |z|+1$, the input cell of $z$ at index $p-\ell$ is blank exactly when $p=\ell$.

**Proof.** By the input-cell definition, if $p-\ell=0$, the cell is blank, and the assumptions $\ell\le p$ imply that this is equivalent to $p=\ell$. Otherwise $p-\ell>0$, so the input cell is the list entry of $z$ at index $p-\ell-1$. The bound $p\le |z|+1$ ensures this is a valid index: $p-\ell-1<|z|$, using $\ell>0$. Hence the optional lookup contains a symbol and is not blank. These two cases establish both directions.
