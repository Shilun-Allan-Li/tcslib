<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: GateOp.id -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The identity gate operation

**Definition.** `FeedForward.GateOp.id α : GateOp α` is the one-input gate that returns its
input unchanged: its index type is `ι := PUnit` and its function is
`func x := x PUnit.unit`.

Composed with `Gate.eval`, which computes `g.op.func (xs ∘ g.inputs)`, a gate built from
`GateOp.id` therefore returns the value of the single predecessor named by its `inputs`
field.

**Remark.** It is an `abbrev`, hence reducible, so `simp` and `decide` see through it; that
is what makes the identity-wire layers of `Circuit.toFeedForward` evaluate away. Note it is
declared inside `namespace FeedForward`, so its full name is `ACP.FeedForward.GateOp.id`
even though `GateOp` itself lives directly in `ACP`.

**Used in.** `BoolCircuit.Circuit.toFeedForward`, where every layer above layer `0` is
wired with this gate to pad the circuit to uniform depth.
