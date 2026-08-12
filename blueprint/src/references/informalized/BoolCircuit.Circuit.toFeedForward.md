<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Circuit.toFeedForward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Embedding a Boolean circuit tree as a layered feedforward circuit

**Definition.** Given `C : BoolCircuit.Circuit n`, `Circuit.toFeedForward C` is a
`FeedForward Bool (Fin n) Unit` of depth `C.depth + 1` whose layer `0` is the input type
`Fin n` and whose every later layer is `Unit`. The single gate from layer `0` to layer `1`
has input index type `Fin n`, is wired to the inputs by the identity, and its gate function
is `C.eval` itself; each gate from layer `d > 0` to layer `d + 1` is the identity gate
`FeedForward.GateOp.id Bool` reading the unique node below it. So the produced object is a
one-output layered circuit that computes `C.eval` at layer `1` and then relays that bit
upward to the output layer.

Fields, as written in Lean:

- `depth := C.depth + 1`.
- `nodes d := if d.val = 0 then Fin n else Unit` — a `Type`-valued branch on the layer index.
- `gates d _` splits on `h : d.val = 0`; both branches transport the domain type across
  `if_pos` / `if_neg` (using that `Fin.castSucc` preserves `.val`) with `Eq.mpr`, so the
  layer-0 gate's `inputs` is `Eq.mpr hdom` and each higher gate's `inputs` is the constant
  `Eq.mpr hdom ()`.
- `nodes_zero := if_pos rfl`.
- `nodes_last` — rewrite by `Fin.val_last`, then `if_neg (Nat.succ_ne_zero C.depth)`.

**Remark.** Despite the surrounding prose about padding an unbalanced tree with identity
wires, this embedding does not decompose `C` at all: the whole circuit is packaged into one
opaque gate whose function is `C.eval`, and the remaining `C.depth` layers are pure relays.
That is why `Circuit.toFeedForward_eval` follows from a constancy lemma over layers, why
`Circuit.toFeedForward_depth` is `rfl`, and why the size bound
`Circuit.toFeedForward_size_le` reduces to `C.depth + 1 ≤ C.size * (C.depth + 1)` via
`Circuit.one_le_size`. The construction is `noncomputable` only because `FeedForward.size`
uses `Nat.card`; the data here is otherwise explicit.

**Used in.** `Circuit.toFeedForward_eval`, `Circuit.toFeedForward_depth`,
`Circuit.toFeedForward_size_le` — the tree → DAG direction of the `FeedForward` /
`BoolCircuit.Circuit` conversion pair.
