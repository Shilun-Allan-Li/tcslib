<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: gateCountBefore_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Gate count of one more layer

**Claim.** For `F : FeedForward (Fin 2) (Fin n) out` with finite layers and
`hd : d + 1 ≤ F.depth`,
`gateCountBefore F (d + 1) hd = gateCountBefore F d _ + Fintype.card (F.nodes ⟨d + 1, _⟩)`
— adding a layer adds exactly the number of nodes on that layer.

**Proof.** Immediate from `simp [gateCountBefore]`; this is the successor branch
of the definition, restated as an equation.

**Remark.** A granular helper, tagged `@[simp]`. The point of stating it is that
`gateCountBefore` is defined by structural recursion carrying a `≤`-proof
argument, so the equation is not available to `rw` until it is packaged as a
lemma; `stepLayerFamily` uses it (via `simp [gateCountBefore, ...]`) to match the
error term of layer `d + 1` against the inductive bound for layer `d`.
