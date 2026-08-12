<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The function computed by a circuit

**Definition.** For `F : FeedForward α inp out` and an input assignment
`xs : inp → α`, `F.eval xs : out → α` sends an output name `o : out` to

`F.evalNode (d := Fin.last F.depth) (F.nodes_last.symm.rec o) xs`,

i.e. it transports `o` backwards along `F.nodes_last : F.nodes (Fin.last F.depth) = out`
to a node of the last layer and evaluates that node with `ACP.FeedForward.evalNode`.

A plain definition; the only content beyond `evalNode` is the transport of the output
name into the last layer.

**Remark.** The companion `eval₁ [Unique out] xs = F.eval xs default` specialises this
to single-output circuits and is what the Razborov–Smolensky statements use.

**Used in.** `ACP.FeedForward.toCircuit_eval`, `Circuit.toFeedForward_eval`, and the
error-probability statements in `RazborovSmolensky/CircuitSize.lean`.
