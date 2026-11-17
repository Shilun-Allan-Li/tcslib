<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.goes_cells -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Traversal of Work Tape Cells

**Claim.** Under the stated register conditions, the program starting at phase zero for cell $\tau$ reaches the start of the next work-tape cell. It updates $i$ and $q$ as specified, preserves the other registers and the input position, appends the tabulated instruction strings for indices $e.i$ through $e.i+2T$, and takes at most $(2T+3)(\mathrm{Lmax}(M)+20)$ steps.

**Proof.** Write $T=T'+1$ and track the computation with a state whose instruction register is $e.i+j$, whose previous-cell register is $0$ at time zero and otherwise $e.i+j-\mathrm{Str}(M,n,z,T)$, and whose inner-loop counter is $c$. First, the single-cell traversal result (`goes_cell_one`) applies at each offset $j$: the phase bits identify whether the cell is at the left endpoint, the middle position $T$ of its block, or the right endpoint. It advances the instruction index by one, emits exactly the tabulated instruction string at that index, and takes at most $\mathrm{Ki}(M)$ steps.

The program then handles the $2T+1$ positions in five pieces. At offset zero it performs one single-cell traversal, copies the value of the step counter into the inner-loop counter (`goes_copyR`), and decrements the latter once (`goes_decR`). The first head-controlled loop now processes the next $T'$ positions: `goes_loop` applies because each body traversal returns to the loop head after advancing one position, while the loop counter decreases by one. At offset $T'+1$, the middle position is traversed separately, then the counter is copied and decremented again. A second application of the same loop argument processes the next $T'$ positions, and a final single-cell traversal handles the last position. Thus the emitted strings, in order, are precisely those indexed by $e.i,e.i+1,\ldots,e.i+2T$.

Composing these segments preserves the input position and leaves every register unchanged except for the specified updates to $i$ and $q$; the loop and copy routines also return the scratch counters to the required values. The list of indices from each segment concatenates to the full consecutive range, using the decomposition of a range into adjacent subranges (`range'_add`) and its representation as an offset map (`range'_eq_map`). Finally, the per-cell traversal bound and the bounds for the two loops and copies, together with $t\le T$, give the stated total step bound.

**Key facts.** `Complexity.UTab.goes_cell_one`, `Complexity.UTab.goes_copyR`, `Complexity.UTab.goes_decR`, `Complexity.CounterProg.goes_loop`, `Complexity.UTab.range'_add`, `Complexity.UTab.range'_eq_map`.
