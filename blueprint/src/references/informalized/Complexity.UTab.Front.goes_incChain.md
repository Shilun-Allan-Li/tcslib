<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_incChain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment-chain Execution

**Claim.** If each label $\ell_i$ for $i<K$ increments register $r$ and proceeds to $\ell_{i+1}$, then for each $i\le K$ the program reaches $\ell_i$ from $\ell_0$ with register $r$ increased by $i$, all other registers and the input position unchanged, and no output appended, in at most $i$ steps.

**Proof.** Proceed by induction on $i$. For $i=0$, the zero-step run stays at the initial state, as given by `goes_nil`. For the successor case, the induction hypothesis gives a run to $\ell_i$ with register $r$ increased by $i$. Since $i<K$, the instruction there increments $r$ and moves to $\ell_{i+1}$; the one-step increment fact (`goes_inc`) supplies this transition. Compose the two runs using `Goes.trans`. The updated register assignment equals the initial assignment with $r$ increased by $i+1$, while every other register is unchanged; `Goes.congr` expresses this equality and adjusts the bound from the composed run to $i+1$.

**Key facts.** `Complexity.UTab.Front.goes_nil`, `Complexity.CounterProg.goes_inc`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`.
