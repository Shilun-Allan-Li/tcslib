---
## Search: 2026-07-08 -- Whitney's inequality helpers (IsBridge, induce, Connected, cardinality)

### 1. SimpleGraph.IsBridge API

**Module**: `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected` (lines 647-763)

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.IsBridge` | `def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop := e ∈ G.edgeSet ∧ Sym2.lift ⟨fun v w => ¬(G \ fromEdgeSet {e}).Reachable v w, ...⟩ e` | Note: uses `G \ fromEdgeSet {e}`, NOT `G.deleteEdges {e}`. They are definitionally equal: `deleteEdges s = G \ fromEdgeSet s`. |
| `SimpleGraph.isBridge_iff` | `G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬(G \ fromEdgeSet {s(u, v)}).Reachable u v` | `Iff.rfl` -- definitional |
| `SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges` | `G.IsBridge s(v, w) ↔ G.Adj v w ∧ ∀ p : G.Walk v w, s(v, w) ∈ p.edges` | Every walk between endpoints must use the bridge edge |
| `SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem` | `G.IsBridge s(v, w) ↔ G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → s(v, w) ∉ p.edges` | Bridge iff adj and edge not in any cycle |
| `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` | `G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges` | Same but for arbitrary `e : Sym2 V` (uses `Sym2.ind`) |
| `SimpleGraph.reachable_delete_edges_iff_exists_walk` | `(G \ fromEdgeSet {s(v, w)}).Reachable v' w' ↔ ∃ p : G.Walk v' w', s(v, w) ∉ p.edges` | Reachability in edge-deleted graph iff walk avoiding that edge |
| `SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle` | `G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges` | Non-bridge characterization via cycles |
| `SimpleGraph.Connected.connected_delete_edge_of_not_isBridge` | `(hG : G.Connected) → (h : ¬ G.IsBridge s(x, y)) → (G.deleteEdges {s(x, y)}).Connected` | Deleting a non-bridge preserves connectivity |

**Key insight**: `IsBridge` is defined using `G \ fromEdgeSet {e}`, which equals `G.deleteEdges {e}` definitionally. But in proofs you may need to convert between them. The definition `deleteEdges s = G \ fromEdgeSet s` (in DeleteEdges.lean line 42).

**No lemma exists** for: "endpoints of a bridge in different components after deletion" -- this must be proved from `isBridge_iff` (the `¬Reachable` part directly says they are not reachable, hence in different components).

### 2. SimpleGraph.induce API

**Module**: `Mathlib.Combinatorics.SimpleGraph.Maps` (lines 190-220)

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.induce` | `abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s := G.comap (Function.Embedding.subtype _)` | It's just `comap` of the subtype embedding |
| `SimpleGraph.induce_adj` | `(G.induce s).Adj u v ↔ G.Adj ↑u ↑v` | `.rfl` -- definitional |
| `SimpleGraph.induce_top` | `(completeGraph V).induce s = completeGraph s` | `@[simp]` |
| `SimpleGraph.induce_singleton_eq_top` | `G.induce {v} = ⊤` | `@[simp]` |
| `SimpleGraph.induceUnivIso` | `G.induce Set.univ ≃g G` | Graph iso; has `.connected_iff` via `Iso.connected_iff` |
| `SimpleGraph.spanningCoe_induce_le` | `(G.induce s).spanningCoe ≤ G` | |
| `SimpleGraph.induceHomOfLE` | `(h : s ≤ s') → G.induce s ↪g G.induce s'` | Graph embedding for subset inclusion |
| `SimpleGraph.comap_monotone` | `Monotone (SimpleGraph.comap f)` | Since `induce = comap`, this gives: if `G ≤ H` then `G.induce s ≤ H.induce s` |

**Module**: `Mathlib.Combinatorics.SimpleGraph.DeleteEdges` (lines 126-131)

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.induce_deleteIncidenceSet_of_notMem` | `(h : x ∉ s) → (G.deleteIncidenceSet x).induce s = G.induce s` | If vertex `x` not in `s`, deleting edges incident to `x` doesn't change `G.induce s` |

**Module**: `Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph` (lines 487-534)

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.connected_induce_iff` | `(G.induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected` | Bridge to Subgraph API |
| `SimpleGraph.induce_union_connected` | `(G.induce s).Connected → (G.induce t).Connected → (s ∩ t).Nonempty → (G.induce (s ∪ t)).Connected` | Union of overlapping connected induced subgraphs |
| `SimpleGraph.induce_pair_connected_of_adj` | `G.Adj u v → (G.induce {u, v}).Connected` | |
| `SimpleGraph.induce_connected_adj_union` | connects `s ∪ t` when `v ∈ s`, `w ∈ t`, `G.Adj v w` | |
| `SimpleGraph.Subgraph.Connected.induce_verts` | `H.Connected → (G.induce H.verts).Connected` | |

**No direct lemma** for `(G.deleteEdges {e}).induce s = (G.induce s).deleteEdges ...`. However, since `induce = comap Subtype.val` and `deleteEdges s = G \ fromEdgeSet s`, and `comap` preserves `sdiff` (by unfolding: `(G \ H).comap f` has adj `G.Adj (f u) (f v) ∧ ¬H.Adj (f u) (f v)` = `G.comap f \ H.comap f`), we get:

`(G.deleteEdges s).induce t = (G.induce t).deleteEdges (Subtype.val ⁻¹' s)` -- but this needs to be proved manually or via `ext` + `simp [deleteEdges_adj, induce_adj]`.

In practice, the adjacency `(G.deleteEdges F).induce S` gives `G.Adj u v ∧ s(u,v) ∉ F` for `u v : S`, which is the same as `(G.induce S).Adj u v ∧ s(↑u, ↑v) ∉ F`. So you can go via `deleteEdges_adj` and `induce_adj`.

### 3. SimpleGraph.Connected / Preconnected / Reachable / ConnectedComponent

**Module**: `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.Reachable.refl` | `G.Reachable u u` | `@[refl]` |
| `SimpleGraph.Reachable.symm` | `G.Reachable u v → G.Reachable v u` | `@[symm]` |
| `SimpleGraph.Reachable.trans` | `G.Reachable u v → G.Reachable v w → G.Reachable u w` | `@[trans]` |
| `SimpleGraph.Reachable.mono` | `(h : G ≤ G') → G.Reachable u v → G'.Reachable u v` | `@[mono]` -- key for lifting walks from subgraph to supergraph |
| `SimpleGraph.Reachable.map` | `(f : G →g G') → G.Reachable u v → G'.Reachable (f u) (f v)` | |
| `SimpleGraph.Preconnected.mono` | `(h : G ≤ G') → G.Preconnected → G'.Preconnected` | `@[mono]` |
| `SimpleGraph.Connected.mono` | `(h : G ≤ G') → G.Connected → G'.Connected` | `@[mono]` |
| `SimpleGraph.Connected.map` | `(f : G →g H) → Surjective f → G.Connected → H.Connected` | |
| `SimpleGraph.Iso.connected_iff` | `(e : G ≃g H) → (G.Connected ↔ H.Connected)` | Used in existing code with `induceUnivIso` |
| `SimpleGraph.connected_iff` | `G.Connected ↔ G.Preconnected ∧ Nonempty V` | `@[mk_iff]` generated |
| `SimpleGraph.connected_iff_exists_forall_reachable` | `G.Connected ↔ ∃ v, ∀ w, G.Reachable v w` | |
| `SimpleGraph.connected_top` | `[Nonempty V] → (completeGraph V).Connected` | `@[simp]` |
| `SimpleGraph.connected_top_iff` | `(completeGraph V).Connected ↔ Nonempty V` | |
| `SimpleGraph.not_connected_bot` | `[Nontrivial V] → ¬(⊥ : SimpleGraph V).Connected` | |
| `SimpleGraph.reachable_bot` | `(⊥ : SimpleGraph V).Reachable u v ↔ u = v` | `@[simp]` |
| `SimpleGraph.Adj.reachable` | `G.Adj u v → G.Reachable u v` | |
| `SimpleGraph.Walk.reachable` | `(p : G.Walk u v) → G.Reachable u v` | |

**ConnectedComponent API** (same module):

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.ConnectedComponent` | `def ConnectedComponent := Quot G.Reachable` | |
| `SimpleGraph.connectedComponentMk` | `(v : V) → G.ConnectedComponent` | `Quot.mk G.Reachable v` |
| `SimpleGraph.ConnectedComponent.eq` | `connectedComponentMk v = connectedComponentMk w ↔ G.Reachable v w` | |
| `SimpleGraph.ConnectedComponent.supp` | `(C : G.ConnectedComponent) → Set V` | `{ v | connectedComponentMk v = C }` |
| `SimpleGraph.ConnectedComponent.mem_supp_iff` | `v ∈ C.supp ↔ connectedComponentMk v = C` | |
| `SimpleGraph.ConnectedComponent.nonempty_supp` | `C.supp.Nonempty` | Every component is nonempty |
| `SimpleGraph.ConnectedComponent.exists_rep` | alias for `nonempty_supp` | |
| `SimpleGraph.ConnectedComponent.toSimpleGraph` | `(C : G.ConnectedComponent) → SimpleGraph C := G.induce C.supp` | |
| `SimpleGraph.ConnectedComponent.connected_toSimpleGraph` | `C.toSimpleGraph.Connected` | Every component is connected |
| `SimpleGraph.ConnectedComponent.reachable_of_mem_supp` | `u ∈ C → v ∈ C → G.Reachable u v` | (line 536) |
| `SimpleGraph.ConnectedComponent.map` | `(φ : G →g G') → G.ConnectedComponent → G'.ConnectedComponent` | |
| `SimpleGraph.Iso.connectedComponentEquiv` | `(φ : G ≃g G') → G.ConnectedComponent ≃ G'.ConnectedComponent` | |
| `SimpleGraph.Preconnected.subsingleton_connectedComponent` | `G.Preconnected → Subsingleton G.ConnectedComponent` | Connected graph has unique component |
| `SimpleGraph.ConnectedComponent.eq_of_common_vertex` | `v ∈ c.supp → v ∈ c'.supp → c = c'` | |
| `SimpleGraph.ConnectedComponent.connectedComponentMk_supp_subset_supp` | `G ≤ G' → v ∈ c'.supp → (G.connectedComponentMk v).supp ⊆ c'.supp` | Subgraph component refines supergraph component |

**Fintype instance for ConnectedComponent** (WalkCounting.lean line 196):

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.ConnectedComponent.instFintype` | `instance : Fintype G.ConnectedComponent` | Requires `[Fintype V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]` |

**deleteEdges monotonicity** (DeleteEdges.lean):

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.deleteEdges_le` | `G.deleteEdges s ≤ G` | `sdiff_le` |
| `SimpleGraph.deleteEdges_anti` | `s₁ ⊆ s₂ → G.deleteEdges s₂ ≤ G.deleteEdges s₁` | |
| `SimpleGraph.deleteEdges_mono` | `G ≤ H → G.deleteEdges s ≤ H.deleteEdges s` | |
| `SimpleGraph.deleteEdges_adj` | `(G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s` | `@[simp]` |
| `SimpleGraph.deleteEdges_deleteEdges` | `(G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s')` | `@[simp]` |
| `SimpleGraph.deleteEdges_empty` | `G.deleteEdges ∅ = G` | `@[simp]` |
| `SimpleGraph.edgeSet_deleteEdges` | `(G.deleteEdges s).edgeSet = G.edgeSet \ s` | |

**Walk.toDeleteEdges** (Walk.lean lines 1419-1446):

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `SimpleGraph.Walk.toDeleteEdges` | `(p : G.Walk v w) → (hp : ∀ e ∈ p.edges, e ∉ s) → (G.deleteEdges s).Walk v w` | Transfer a walk to edge-deleted graph if no edge is in `s` |
| `SimpleGraph.Walk.toDeleteEdge` | convenience wrapper for singleton `{e}` | (line 1439-1442) |
| `SimpleGraph.Walk.map_toDeleteEdges_eq` | `Walk.map (.ofLE (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p` | Round-trip: map back to original graph recovers original walk |

### 4. Cardinality Helpers

**Module**: `Mathlib.Data.Fintype.Card`

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `Fintype.card_subtype_compl` | `Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x }` | `@[simp]` -- KEY for `|V \ S| = |V| - |S|` |
| `Fintype.card_compl_set` | `Fintype.card (↥sᶜ) = Fintype.card α - Fintype.card s` | Same but for `Set` complement |
| `Fintype.card_coe` | `Fintype.card ↥(s : Finset α) = s.card` | `@[simp]` |
| `Set.toFinset_card` | `s.toFinset.card = Fintype.card s` | (line 94) |
| `Fintype.card_subtype` | `Fintype.card { x // p x } = (Finset.univ.filter p).card` | |
| `Fintype.card_subtype_mono` | `p ≤ q → Fintype.card { x // p x } ≤ Fintype.card { x // q x }` | |
| `Fintype.card_subtype_lt` | `(∃ x, ¬p x) → Fintype.card { x // p x } < Fintype.card α` | |

**Module**: `Mathlib.Data.Finset.Card`

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `Finset.card_compl` | `sᶜ.card = Fintype.card α - s.card` | |
| `Finset.card_add_card_compl` | `s.card + sᶜ.card = Fintype.card α` | `@[simp]` |
| `Finset.card_compl_add_card` | `sᶜ.card + s.card = Fintype.card α` | `@[simp]` |
| `Finset.card_insert_of_notMem` | `a ∉ s → (insert a s).card = s.card + 1` | |
| `Finset.card_insert_le` | `(insert a s).card ≤ s.card + 1` | |
| `Finset.card_insert_of_mem` | `a ∈ s → (insert a s).card = s.card` | |
| `Finset.card_univ_diff` | `(univ \ s).card = Fintype.card α - s.card` | |

**Module**: `Mathlib.Data.Fintype.Sets`

| Lemma / Tactic | Signature | Notes |
|---|---|---|
| `Set.toFinset_compl` | `sᶜ.toFinset = s.toFinsetᶜ` | (line 144) |

### Relationships Critical for the Three Sorrys

**SORRY #13** (`exists_isVertexCut_singleton_of_isBridge`): Given a bridge `e = s(u,v)`, the `isBridge_iff` gives `¬(G \ fromEdgeSet {e}).Reachable u v`. Since `G.deleteEdges {e} = G \ fromEdgeSet {e}` definitionally, this means `u` and `v` are in different connected components of `G.deleteEdges {e}`. With `|V| ≥ 3`, at least one component has `≥ 2` vertices. Use `ConnectedComponent.eq` (reachable iff same component) and `ConnectedComponent.nonempty_supp`. The key tool for showing `{u}` or `{v}` is a vertex cut is: show that removing `u` disconnects `G` by finding two vertices in different components of `G.induce ({u}ᶜ)`.

**SORRY #14** (`vertexConn_le_succ_of_vertexCut_deleteEdge`): Main case split on whether `G.induce (Sᶜ)` is connected. Use `Connected.mono` with `deleteEdges_le` to relate `(G.deleteEdges {e}).induce Sᶜ` connectivity to `G.induce Sᶜ` connectivity. When `G.induce (Sᶜ)` is connected but `(G.deleteEdges {e}).induce (Sᶜ)` is not, `e` is a bridge of `G.induce (Sᶜ)`, then apply sorry #13.

**SORRY #15** (`vertexConnectivity_le_edgeConnectivity`): Strong induction on `edgeConnectivity`. Use `edgeConnectivity_deleteEdges_singleton` and `vertexConn_le_succ_of_vertexCut_deleteEdge`.

### Key conversion: `deleteEdges {e}` vs `G \ fromEdgeSet {e}`

These are **definitionally equal**: `deleteEdges s = G \ fromEdgeSet s`. So `G.deleteEdges {s(u,v)}` and `G \ fromEdgeSet {s(u,v)}` are interchangeable without any lemma. The `IsBridge` definition uses the `\ fromEdgeSet` form, but `deleteEdges_adj` works on the `deleteEdges` form. Both should reduce to the same thing via `rfl` or `show`.

---
