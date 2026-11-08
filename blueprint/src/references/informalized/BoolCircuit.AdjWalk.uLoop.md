<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.uLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Loop Behavior

**Claim.** Under the stated register bounds and index conditions, the walk in state $uL$ either halts at the indicated position with the specified answer, or, if the unary word has been fully traversed, reaches state $aN$ with the updated registers and no answer, while respecting the bound $B$.

**Proof.** Proceed by induction on the number $d$ of ones in the word, keeping the starting register values $W$ and $k$ arbitrary subject to the hypotheses. The proof uses the established characterization of the emitted-site segment (`BoolCircuit.AdjWalk.Em.emit`), the composition rule for concatenating such segments (`BoolCircuit.AdjWalk.Em.append`), and the ability to weaken the segment's endpoint condition (`BoolCircuit.AdjWalk.Em.mono`).

1. If $d=0$, the relation $W+d=U$ forces $W=U$. The walk's next step from state $uL$ compares the fourth register with the third; since both equal $U$, it emits the end site $uEnd$. The emission result gives the required halting or reachability behavior, and the register bounds follow from the hypotheses.

2. Suppose $d$ is positive. The relation $W+d=U$ implies $W<U$, so the comparison at $uL$ selects the $uOne$ site. The emission result accounts for this first site and advances the first register from $k$ to $k+1$, with the other registers unchanged. This accounts for the initial one in the word, and the emission and append results combine it with the remaining segment.

3. After the emitted $uOne$ site, the walk increments the fourth register and returns to $uL$. The new values are $W+1$ and $k+1$, and the remaining word has $d$ fewer ones. Apply the induction hypothesis with these updated values; the index and bound conditions transfer by the given inequalities. If the walk reaches the continuation state, the induction endpoint has first register $(k+1)+(d-1)+1=k+d+1$ and fourth register $U$. The endpoint condition is therefore exactly the stated configuration. The register bound at each step follows from the bounds on $V,U$ and the assumed bound on $k+d+1$.

**Key facts.** `BoolCircuit.AdjWalk.gd_rg`, `BoolCircuit.AdjWalk.Em.step`, `BoolCircuit.AdjWalk.rg_2`, `BoolCircuit.AdjWalk.rg_3`, `BoolCircuit.AdjWalk.Em.emit`, `BoolCircuit.AdjWalk.Em.mono`, `BoolCircuit.AdjWalk.Em.append`, `BoolCircuit.AdjWalk.upd_3`.
