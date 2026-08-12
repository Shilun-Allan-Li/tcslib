<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A gate together with its input wiring

**Definition.** `Gate α domain` is a two-field structure:

* `op : GateOp α` — the operation the gate performs, itself a pair of an input index
  type `op.ι` and a function `op.func : (op.ι → α) → α`;
* `inputs : op.ι → domain` — the wiring, saying which element of `domain` each input
  slot of the gate reads from.

So a `Gate` separates *what* is computed (`op`) from *where the arguments come from*
(`inputs`). The index type `op.ι` is arbitrary, so fan-in is unbounded and need not be
finite; finiteness, when needed, is supplied separately as a `Fintype (…).op.ι`
hypothesis.

**Remark.** In a `FeedForward` circuit `domain` is instantiated with the previous
layer's node type, which is what forces the wiring to be acyclic by construction.

**Used in.** The `gates` field of `ACP.FeedForward`; evaluated by
`ACP.FeedForward.Gate.eval`.
