<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Gate.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating one gate

**Definition.** Given a gate `g : Gate α domain` and an assignment `xs : domain → α` of
values to the nodes it may read from,

`g.eval xs = g.op.func (xs ∘ g.inputs)`.

That is: pull the value of each input slot through the wiring `g.inputs`, then apply the
gate's operation `g.op.func` to the resulting family. A one-line definition with no
side conditions — in particular `domain` need not be finite.

**Used in.** The successor step of `ACP.FeedForward.evalNode`, and hence in
`nodeToCircuit_eval`, where the identity `evalNode (d+1) = Gate.eval (gates d _) ∘ …`
is unfolded with `simp only [FeedForward.Gate.eval]`.
