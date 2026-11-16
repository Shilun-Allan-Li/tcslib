/-
PROPOSED ADDITIONS to `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` (shared file).
DRAFT (briefs/lattice-gsw): not compiled, not applied. This text is appended inside the
existing `namespace BoolCircuit` of that file, after `DAGCircuit.depthAt_gate`. It needs the
owner's/maintainer's approval as a shared-file change (policy §1, "Definitions land with their
lemmas"; Rule 10: readers of a definition go beside it, in its own file).

Why: the GSW depth theorem reads gate depths and runs a second evaluator alongside
`DAGGate.eval`. `DAGGate.depth`, `DAGCircuit.depths`, `depthAt` and `depth` predate the
reader rule and have no published equation; style-lint check 8 lists them. The relational
`runWith_rel` is the general form of `SecureComputation.runWith_sim`
(SecureComputation/Garbling.lean:94), which is the special case `R v a b ↔ b = W v a`. It is a
host lemma ("Hosts come first"), so it belongs in the circuit layer, not in a GSW file.
`Garbling.lean` is under audit (#323) and is not touched; harvesting `runWith_sim` onto
`runWith_rel` is a later dedup item, not part of this change.
-/

/-- A gate's depth is one more than the maximum depth of the vertices it reads, vertex `v`'s
depth being `ds.getD v 0` [AB09, Def 6.1, depth of a vertex]. -/
theorem DAGGate.depth_eq (g : DAGGate) (ds : List ℕ) :
    g.depth ds = 1 + (g.args.map fun a => ds.getD a 0).foldr max 0 := rfl

/-- Every vertex a gate reads is strictly shallower than the gate.

**Proof sketch.** By `DAGGate.depth_eq`, it suffices that `ds.getD a 0` is at most the
`foldr max 0` of the mapped list when `a ∈ g.args`; induct on `g.args` with `le_max_left` /
`le_max_right` and `List.mem_cons`. -/
theorem DAGGate.getD_lt_depth (g : DAGGate) (ds : List ℕ) {a : ℕ} (ha : a ∈ g.args) :
    ds.getD a 0 < g.depth ds := by
  sorry

namespace DAGCircuit

variable {n : ℕ} (C : DAGCircuit n)

/-- The vertex-depth list runs `DAGGate.depth` from `n` zeros [AB09, Def 6.1]. -/
theorem depths_eq : C.depths = runWith DAGGate.depth C.gates (List.replicate n 0) := rfl

/-- The depth of vertex `v` is entry `v` of the depth list, `0` out of range. -/
theorem depthAt_eq (v : ℕ) : C.depthAt v = C.depths.getD v 0 := rfl

/-- The circuit depth is the depth of its output vertex [AB09, Def 6.1]. -/
theorem depth_eq : C.depth = C.depthAt C.output := rfl

end DAGCircuit

/-- **Relational indexed simulation of `runWith`.** Two evaluators run the same gate list from
initial data related vertex by vertex by `R v`. If, at gate `i`, related data on the gate's
inputs always produce related outputs at vertex `L + i`, then the two runs are related at
every vertex. Technical host lemma; `SecureComputation.runWith_sim` is the functional special
case.

**Proof sketch.** Strong induction on the vertex, exactly as `runWith_sim`: input vertices
are the initial relation (`runWith_getD_of_lt`); a gate vertex `L + i` reads both runs'
prefixes (`runWith_getD_gate`), whose argument entries agree with the full runs
(`runWith_getD_take`) and are related by the induction hypothesis, since acyclicity puts every
argument below `L + i`. -/
theorem runWith_rel {α β : Type} (fA : DAGGate → List α → α) (fB : DAGGate → List β → β)
    (R : ℕ → α → β → Prop) (dA : α) (dB : β) (gs : List DAGGate)
    (initA : List α) (initB : List β) (hlen : initB.length = initA.length)
    (hinit : ∀ v < initA.length, R v (initA.getD v dA) (initB.getD v dB))
    (hacyc : ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < initA.length + i)
    (hgate : ∀ (i : ℕ) (h : i < gs.length) (vA : List α) (vB : List β),
      vA.length = initA.length + i → vB.length = initA.length + i →
      (∀ a ∈ (gs[i]).args, R a (vA.getD a dA) (vB.getD a dB)) →
      R (initA.length + i) (fA gs[i] vA) (fB gs[i] vB)) :
    ∀ v < initA.length + gs.length,
      R v ((runWith fA gs initA).getD v dA) ((runWith fB gs initB).getD v dB) := by
  sorry
