# Mathlib 4 Lemma Catalogue — Euler Tours & Hamilton Cycles (Bondy & Murty Ch. 4)

Toolchain: `leanprover/lean4:v4.25.0-rc2`. Mathlib pre-built.
All signatures below were verified either by grepping
`/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/…` or with a
`#check` compiled by `lake env lean` (crucial names all `#check`-verified).

Everything lives under `namespace SimpleGraph`. Members shown as `Walk.Foo`
have fully-qualified name `SimpleGraph.Walk.Foo`. `open SimpleGraph` assumed.

Common instance requirements you almost always need in scope:
`[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`.

---

## A. Eulerian API — `Mathlib/Combinatorics/SimpleGraph/Trails.lean`

Requires `[DecidableEq V]` throughout. Degree lemmas add `[Fintype V] [DecidableRel G.Adj]`.

| Name | Signature |
|---|---|
| `SimpleGraph.Walk.IsEulerian` (def) | `{p : G.Walk u v} : Prop := ∀ e, e ∈ G.edgeSet → p.edges.count e = 1` |
| `SimpleGraph.Walk.IsEulerian.isTrail` | `(h : p.IsEulerian) : p.IsTrail` |
| `SimpleGraph.Walk.IsEulerian.mem_edges_iff` | `(h : p.IsEulerian) {e : Sym2 V} : e ∈ p.edges ↔ e ∈ G.edgeSet` |
| `SimpleGraph.Walk.isEulerian_iff` | `(p : G.Walk u v) : p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges` |
| `SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem` | `(h : p.IsTrail) (hc : ∀ e, e ∈ G.edgeSet → e ∈ p.edges) : p.IsEulerian` |
| `SimpleGraph.Walk.IsTrail.isEulerian_iff` | `(hp : p.IsTrail) : p.IsEulerian ↔ p.edgeSet = G.edgeSet` |
| `SimpleGraph.Walk.IsEulerian.edgeSet_eq` | `(h : p.IsEulerian) : p.edgeSet = G.edgeSet` |
| `SimpleGraph.Walk.IsEulerian.fintypeEdgeSet` | `(h : p.IsEulerian) : Fintype G.edgeSet` (def) |
| `SimpleGraph.Walk.IsEulerian.edgesFinset_eq` | `[Fintype G.edgeSet] (h : p.IsEulerian) : h.isTrail.edgesFinset = G.edgeFinset` |
| `SimpleGraph.Walk.IsTrail.edgesFinset` | `(h : p.IsTrail) : Finset (Sym2 V)` (abbrev = `⟨p.edges, h.edges_nodup⟩`) |
| `SimpleGraph.Walk.IsTrail.even_countP_edges_iff` | `(ht : p.IsTrail) (x : V) : Even (p.edges.countP fun e => x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v` |

### CRUCIAL degree-parity lemmas (verified via `#check`)

All three take `{p : G.Walk u v}` (a walk from `u` to `v`) — the SAME statement
covers both the closed tour (`u = v`) and the open trail (`u ≠ v`); the parity
result is driven by the `u ≠ v` hypothesis inside the RHS.

**`SimpleGraph.Walk.IsEulerian.even_degree_iff`**
```
{V} {G : SimpleGraph V} [DecidableEq V] {x u v : V} {p : G.Walk u v}
  (ht : p.IsEulerian) [Fintype V] [DecidableRel G.Adj] :
  Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v
```
Interpretation:
- **Closed euler tour** `p : G.Walk u u` (`u = v`): the hypothesis `u ≠ v` is
  false, so the RHS `(u ≠ v → …)` is vacuously `True` for every `x`. Hence
  **every** vertex has even degree.
- **Open euler trail** `p : G.Walk u v` with `u ≠ v`: `Even (G.degree x) ↔
  x ≠ u ∧ x ≠ v`, i.e. exactly the two endpoints `u`, `v` have ODD degree, all
  others even.

**`SimpleGraph.Walk.IsEulerian.card_filter_odd_degree`**
```
[Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
  (ht : p.IsEulerian) {s : Finset V}
  (h : s = Finset.univ.filter fun v => Odd (G.degree v)) :
  s.card = 0 ∨ s.card = 2
```
The `Finset` version: the set of odd-degree vertices has cardinality 0 or 2
(0 for a closed tour, 2 for an open trail). Note the arg is passed as an
equation `h : s = …filter…` (convenient for `rw`/`subst`).

**`SimpleGraph.Walk.IsEulerian.card_odd_degree`**
```
[Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v} (ht : p.IsEulerian) :
  Fintype.card { v : V | Odd (G.degree v) } = 0 ∨
  Fintype.card { v : V | Odd (G.degree v) } = 2
```
Same fact as `card_filter_odd_degree` but stated with `Fintype.card` of the
`Set` subtype.

> NOTE: Mathlib does NOT give the converse (existence of an Eulerian trail from
> the degree condition) — this is an explicit TODO in the file header.
> `⚠ NOT FOUND — must be built` if you need the "if degrees even ⇒ euler tour
> exists" direction (Euler's theorem forward direction).

---

## B. Hamiltonian API — `Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean`

Requires `[DecidableEq α]` throughout (`α` is the vertex type here, `G : SimpleGraph α`).
Graph-level `IsHamiltonian` and length lemmas add `[Fintype α]`.

### Hamiltonian paths (`Walk.IsHamiltonian`)

| Name | Signature |
|---|---|
| `SimpleGraph.Walk.IsHamiltonian` (def) | `(p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1` |
| `SimpleGraph.Walk.IsHamiltonian.mem_support` `@[simp]` | `(hp : p.IsHamiltonian) (c : α) : c ∈ p.support` |
| `SimpleGraph.Walk.IsHamiltonian.isPath` | `(hp : p.IsHamiltonian) : p.IsPath` |
| `SimpleGraph.Walk.IsPath.isHamiltonian_of_mem` | `(hp : p.IsPath) (hp' : ∀ w, w ∈ p.support) : p.IsHamiltonian` |
| `SimpleGraph.Walk.IsPath.isHamiltonian_iff` | `(hp : p.IsPath) : p.IsHamiltonian ↔ ∀ w, w ∈ p.support` |
| `SimpleGraph.Walk.IsHamiltonian.map` | `{H} (f : G →g H) (hf : Bijective f) (hp : p.IsHamiltonian) : (p.map f).IsHamiltonian` |
| `SimpleGraph.Walk.IsHamiltonian.fintype` | `(hp : p.IsHamiltonian) : Fintype α` (def) |
| `SimpleGraph.Walk.IsHamiltonian.support_toFinset` | `[Fintype α] (hp) : p.support.toFinset = Finset.univ` |
| `SimpleGraph.Walk.IsHamiltonian.length_eq` | `[Fintype α] (hp) : p.length = Fintype.card α - 1` |
| `SimpleGraph.Walk.IsHamiltonian.length_support` | `[Fintype α] (hp) : p.support.length = Fintype.card α` |

### Hamiltonian cycles (`Walk.IsHamiltonianCycle`)

**It is a `structure … extends p.IsCycle`** (a `Prop`-valued structure), taking
`(p : G.Walk a a)`:
```
structure IsHamiltonianCycle (p : G.Walk a a) : Prop extends p.IsCycle where
  isHamiltonian_tail : p.tail.IsHamiltonian
```
So it "extends" `SimpleGraph.Walk.IsCycle p` and adds one field
`isHamiltonian_tail : p.tail.IsHamiltonian` (Hamiltonicity is stated on the
TAIL, because the start vertex appears twice in a closed cycle's support).

| Name | Signature |
|---|---|
| `SimpleGraph.Walk.IsHamiltonianCycle` | structure, see above; `.toIsCycle`, `.isHamiltonian_tail` are the projections |
| `SimpleGraph.Walk.IsHamiltonianCycle.isCycle` | `(hp : p.IsHamiltonianCycle) : p.IsCycle` (= `hp.toIsCycle`) |
| `SimpleGraph.Walk.isHamiltonianCycle_isCycle_and_isHamiltonian_tail` | `p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.tail.IsHamiltonian` |
| `SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one` | `p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ a, (support p).tail.count a = 1` |
| `SimpleGraph.Walk.IsHamiltonianCycle.mem_support` | `(hp) (b : α) : b ∈ p.support` (visits every vertex) |
| `SimpleGraph.Walk.IsHamiltonianCycle.length_eq` | `[Fintype α] (hp) : p.length = Fintype.card α` |
| `SimpleGraph.Walk.IsHamiltonianCycle.count_support_self` | `(hp) : p.support.count a = 2` (start vertex counted twice) |
| `SimpleGraph.Walk.IsHamiltonianCycle.support_count_of_ne` | `(hp) (h : a ≠ b) : p.support.count b = 1` |
| `SimpleGraph.Walk.IsHamiltonianCycle.map` | `{H} (f : G →g H) (hf : Bijective f) (hp) : (p.map f).IsHamiltonianCycle` |

There is NO `.support = univ` lemma stated directly; use `.mem_support` +
`Finset.eq_univ_iff_forall`, or `.length_eq`.

### Graph-level Hamiltonicity (`SimpleGraph.IsHamiltonian`) — needs `[Fintype α]`

```
def SimpleGraph.IsHamiltonian (G : SimpleGraph α) : Prop :=
  Fintype.card α ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle
```
(By convention the singleton graph is Hamiltonian — hence the `card ≠ 1` guard.)

| Name | Signature |
|---|---|
| `SimpleGraph.IsHamiltonian` (def) | see above |
| `SimpleGraph.IsHamiltonian.mono` | `{H} (hGH : G ≤ H) (hG : G.IsHamiltonian) : H.IsHamiltonian` |
| `SimpleGraph.IsHamiltonian.connected` | `(hG : G.IsHamiltonian) : G.Connected` |

**Constructing a Hamilton cycle on `⊤ / completeGraph / Fintype`:**
`⚠ NOT FOUND — must be built.` Grep of all of Mathlib shows `IsHamiltonianCycle`
is referenced ONLY inside `Hamiltonian.lean`. There is:
- No lemma "`(⊤ : SimpleGraph V).IsHamiltonian`" / "`completeGraph V` is Hamiltonian".
- No construction of a Hamilton cycle from a `Fintype`/cyclic order.
- `SimpleGraph.cycleGraph (n : ℕ) : SimpleGraph (Fin n)` EXISTS
  (`Mathlib/Combinatorics/SimpleGraph/Circulant.lean:60`) with
  `cycleGraph_two_eq_top` etc., but NO lemma that its canonical walk is an
  `IsHamiltonianCycle`. Building the complete-graph / Dirac-type existence
  results is downstream work.

---

## C. Edge add & graph operations

### Single-edge graph — `Mathlib/Combinatorics/SimpleGraph/Operations.lean` (`section AddEdge`)

Base vars `(s t : V)`. `edge` is `SimpleGraph.edge`.

| Name | Signature |
|---|---|
| `SimpleGraph.edge` (def) | `(s t : V) : SimpleGraph V := fromEdgeSet {s(s, t)}` |
| `SimpleGraph.edge_adj` | `(v w : V) : (edge s t).Adj v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) ∧ v ≠ w` |
| `SimpleGraph.adj_edge` | `{v w} : (edge s t).Adj v w ↔ s(s, t) = s(v, w) ∧ v ≠ w` |
| `SimpleGraph.edge_comm` | `edge s t = edge t s` |
| `SimpleGraph.edge_self_eq_bot` `@[simp]` | `edge s s = ⊥` |
| `SimpleGraph.sup_edge_self` | `G ⊔ edge s s = G` |
| `SimpleGraph.lt_sup_edge` | `(hne : s ≠ t) (hn : ¬ G.Adj s t) : G < G ⊔ edge s t` |
| `SimpleGraph.edge_le_iff` | `{v w} : edge v w ≤ G ↔ v = w ∨ G.Adj v w` |
| `SimpleGraph.edge_edgeSet_of_ne` | `(h : s ≠ t) : (edge s t).edgeSet = {s(s, t)}` |
| `SimpleGraph.sup_edge_of_adj` | `(h : G.Adj s t) : G ⊔ edge s t = G` |
| `SimpleGraph.disjoint_edge` | `{u v} : Disjoint G (edge u v) ↔ ¬G.Adj u v` |
| `SimpleGraph.sdiff_edge` | `{u v} (h : ¬G.Adj u v) : G \ edge u v = G` |
| `SimpleGraph.edgeFinset_sup_edge` | `[Fintype (G ⊔ edge s t).edgeSet] (hn : ¬G.Adj s t) (h : s ≠ t) : (G ⊔ edge s t).edgeFinset = G.edgeFinset.cons s(s,t) _` |
| `SimpleGraph.card_edgeFinset_sup_edge` | `[Fintype V] [DecidableRel G.Adj] [Fintype (G ⊔ edge s t).edgeSet] (hn : ¬G.Adj s t) (h : s ≠ t) : #(G ⊔ edge s t).edgeFinset = #G.edgeFinset + 1` |

`⚠ NOT FOUND` — no dedicated lemma "`(G ⊔ edge s t).degree` = `G.degree + …`"
for the degree change of an endpoint under adding an edge. Derive from
`degree = #neighborFinset`, `neighborFinset` of `⊔`, and `edge_adj`; or use
`SimpleGraph.degree_le_of_le` (monotone) + counting. (Related: the
`replaceVertex` file has `#… = #G.edgeFinset + G.degree s - G.degree t` lemmas,
not directly the single-edge degree bump.)

### Walk operations — `Mathlib/Combinatorics/SimpleGraph/Walk.lean`

| Name | Signature |
|---|---|
| `SimpleGraph.Walk.append` (def) | `{u v w} : G.Walk u v → G.Walk v w → G.Walk u w` |
| `SimpleGraph.Walk.concat` (def) | `(p : G.Walk u v) (h : G.Adj v w) : G.Walk u w := p.append (cons h nil)` |
| `SimpleGraph.Walk.length_append` `@[simp]` | `(p : G.Walk u v) (q : G.Walk v w) : (p.append q).length = p.length + q.length` |
| `SimpleGraph.Walk.support_append` | `(p q) : (p.append q).support = p.support ++ q.support.tail` |
| `SimpleGraph.Walk.edges_append` `@[simp]` | `(p q) : (p.append q).edges = p.edges ++ q.edges` |
| `SimpleGraph.Walk.tail` (def) | `(p : G.Walk u v) : G.Walk (p.snd) v := p.drop 1` (drops the first dart) |
| `SimpleGraph.Walk.tail_cons` | `(h : G.Adj u v) (p : G.Walk v w) : (cons h p).tail = …` (rewrites `cons`.tail) |
| `SimpleGraph.Walk.tail_cons_nil` | `(h : G.Adj u v) : (cons h .nil).tail = .nil` |
| `SimpleGraph.Walk.cons_support_tail` `@[simp]` | `(p) (hp : ¬p.Nil) : u :: p.tail.support = p.support` |
| `SimpleGraph.Walk.length_tail_add_one` `@[simp]` | `(hp : ¬p.Nil) : p.tail.length + 1 = p.length` |
| `SimpleGraph.Walk.support_tail` `@[simp]` | `(p : G.Walk u u) (hp : ¬p.Nil) : p.tail.support = p.support.tail` |
| `SimpleGraph.Walk.support_tail_of_not_nil` | `(p : G.Walk u v) (hnp : ¬p.Nil) : p.tail.support = p.support.tail` (general endpoints) |
| `SimpleGraph.Walk.drop` (def) | `(p : G.Walk u v) (n : ℕ) : G.Walk (p.getVert n) v` (tail = `drop 1`) |

### Delete edges — `Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean`

| Name | Signature |
|---|---|
| `SimpleGraph.deleteEdges` (def) | `(s : Set (Sym2 V)) : SimpleGraph V := G \ fromEdgeSet s` |
| `SimpleGraph.deleteEdges_adj` `@[simp]` | `(G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s` |
| `SimpleGraph.deleteEdges_deleteEdges` | `(s s') : (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s')` |
| `SimpleGraph.deleteEdges_eq_inter_edgeSet` | `(s) : G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet)` |
| `SimpleGraph.deleteEdges_sdiff_eq_of_le` | `{H} (h : H ≤ G) : G.deleteEdges (G.edgeSet \ H.edgeSet) = …` |

### `⊤` / complete graph / compl — `Mathlib/Combinatorics/SimpleGraph/Basic.lean`

| Name | Signature |
|---|---|
| `SimpleGraph.top_adj` | `(v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w` |
| `SimpleGraph.completeGraph` (def) | `completeGraph V : SimpleGraph V` |
| `SimpleGraph.completeGraph_eq_top` | `completeGraph V = ⊤` |
| `SimpleGraph.compl` | complement; `compl_adj : Gᶜ.Adj v w ↔ v ≠ w ∧ ¬G.Adj v w` (in Basic) |

---

## D. Degrees / handshake / minDegree / bridges

### Degrees & degree-sum — `Finite.lean`, `DegreeSum.lean`

| Name | Signature |
|---|---|
| `SimpleGraph.degree` (def) | `(v : V) [Fintype (G.neighborSet v)] : ℕ := #(G.neighborFinset v)` |
| `SimpleGraph.minDegree` (def) | `[Fintype V] [DecidableRel G.Adj] : ℕ` (`Finite.lean:324`) |
| `SimpleGraph.minDegree_le_degree` | `[Fintype V] [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v` |
| `SimpleGraph.le_minDegree_of_forall_le_degree` | `[Nonempty V] (k) (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree` |
| `SimpleGraph.exists_minimal_degree_vertex` | `[Nonempty V] : ∃ v, G.minDegree = G.degree v` |
| `SimpleGraph.minDegree_le_minDegree` | `{H} (hle : G ≤ H) : G.minDegree ≤ H.minDegree` |
| `SimpleGraph.minDegree_lt_card` | `[Nonempty V] : G.minDegree < Fintype.card V` |
| `SimpleGraph.degree_le_of_le` | `{H} [Fintype (H.neighborSet v)] (hle : G ≤ H) : G.degree v ≤ H.degree v` |
| `SimpleGraph.sum_degrees_eq_twice_card_edges` | `[Fintype V] [DecidableRel G.Adj] : ∑ v, G.degree v = 2 * #G.edgeFinset` |
| `SimpleGraph.sum_degrees_support_eq_twice_card_edges` | `∑ v ∈ G.support, G.degree v = 2 * #G.edgeFinset` |
| `SimpleGraph.even_card_odd_degree_vertices` | `[Fintype V] [DecidableRel G.Adj] : Even #{v \| Odd (G.degree v)}` (handshaking lemma) |
| `SimpleGraph.odd_card_odd_degree_vertices_ne` | `[Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v) (h : Odd (G.degree v)) : Odd #{w \| w ≠ v ∧ Odd (G.degree w)}` |

### Bridges — `Connectivity/Connected.lean` (also aliased in `Acyclic.lean`)

```
def SimpleGraph.IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧
    Sym2.lift ⟨fun v w => ¬(G \ fromEdgeSet {e}).Reachable v w, …⟩ e
```

| Name | Signature |
|---|---|
| `SimpleGraph.IsBridge` (def) | see above |
| `SimpleGraph.isBridge_iff` | `{u v} : G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬(G \ fromEdgeSet {s(u, v)}).Reachable u v` |
| `SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges` | `{v w} : G.IsBridge s(v,w) ↔ G.Adj v w ∧ ∀ p : G.Walk v w, s(v,w) ∈ p.edges` |
| `SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem` | `{v w} : G.IsBridge s(v,w) ↔ G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → s(v,w) ∉ p.edges` |
| `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` | `{e} : G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ …cycle…, e ∉ p.edges` |
| `SimpleGraph.Connected.connected_delete_edge_of_not_isBridge` | `(hG : G.Connected) {x y} (h : ¬ G.IsBridge s(x,y)) : (G.deleteEdges {s(x,y)}).Connected` |
| `SimpleGraph.reachable_delete_edges_iff_exists_walk` | `{v w v' w'} : (G \ fromEdgeSet {s(v,w)}).Reachable v' w' ↔ ∃ p : G.Walk v' w', s(v,w) ∉ p.edges` |
| `SimpleGraph.isAcyclic_iff_forall_adj_isBridge` | `G.IsAcyclic ↔ ∀ ⦃v w⦄, G.Adj v w → G.IsBridge s(v,w)` |
| `SimpleGraph.isAcyclic_iff_forall_edge_isBridge` | `G.IsAcyclic ↔ ∀ ⦃e⦄, e ∈ G.edgeSet → G.IsBridge e` |

`⚠ NOT FOUND` — no direct lemma "removing a bridge increases the number of
connected components by exactly one" (the Ch.4 Euler-tour argument). You have
`connected_delete_edge_of_not_isBridge` (non-bridge ⇒ stays connected) but the
component-count delta for a bridge must be built.

---

## E. ConnectedComponent / component count

Files: `Connectivity/Connected.lean`, `Connectivity/WalkCounting.lean`.

| Name | Signature |
|---|---|
| `SimpleGraph.ConnectedComponent` | `:= Quotient G.reachableSetoid` (the quotient of `V` by reachability) |
| `Fintype G.ConnectedComponent` (instance) | AVAILABLE for `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`. Declared as an anonymous `instance : Fintype G.ConnectedComponent` in `WalkCounting.lean:196` via `Quotient.fintype` + `DecidableRel G.Reachable`. So `Fintype.card G.ConnectedComponent` typechecks directly under those instances — no manual construction needed. |
| `DecidableRel G.Reachable` (instance) | `WalkCounting.lean:193`, from `reachable_iff_exists_finsetWalkLength_nonempty` |
| `SimpleGraph.ConnectedComponent.supp` | `(c) : Set V` — the support/vertex set of a component |
| `SimpleGraph.ConnectedComponent.instFintypeSupp` / `instDecidableMemSupp` | `[Fintype V]…` decidability + fintype of `c.supp` (WalkCounting) |
| `SimpleGraph.induce` | `(s : Set V) : SimpleGraph s`; `induce_adj {u v : s} : (G.induce s).Adj u v ↔ G.Adj u v` (`Maps.lean:203`) |
| `SimpleGraph.Subgraph.induce` | `(G' : G.Subgraph) (s : Set V) : G.Subgraph` with `Adj u v := u ∈ s ∧ v ∈ s ∧ G'.Adj u v` |
| `SimpleGraph.Subgraph.deleteVerts` | `(s : Set V) : G.Subgraph`; `deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s`; `deleteVerts_adj : (G'.deleteVerts s).Adj u v ↔ u ∈ G'.verts ∧ u ∉ s ∧ v ∈ G'.verts ∧ v ∉ s ∧ G'.Adj u v` |
| `(⊤ : G.Subgraph)` | the full spanning subgraph; combine with `.deleteVerts s` for vertex deletion |

`⚠ NOT FOUND` — **no** off-the-shelf lemma that `Fintype.card G.ConnectedComponent`
is monotone under `G ≤ H` (adding edges cannot increase the component count),
nor a spanning-subgraph component-count inequality. The `Represents.lean` /
`WalkCounting.lean` machinery is about odd components (Tutte), not a clean
`card_connectedComponent_le_of_le`. Must be built if the proof needs it.
(Available building block: `SimpleGraph.disjiUnion_supp_toFinset_eq_supp_toFinset`
for `G ≤ G'`, `WalkCounting.lean:219`.)

---

## F. Finset / Multiset / Nat arithmetic helpers (all `#check`-verified)

| Name | Signature |
|---|---|
| `Finset.card_union_add_card_inter` | `[DecidableEq α] (s t : Finset α) : (s ∪ t).card + (s ∩ t).card = s.card + t.card` |
| `Finset.card_inter_add_card_union` | `[DecidableEq α] (s t) : (s ∩ t).card + (s ∪ t).card = s.card + t.card` (mirror) |
| `Finset.card_union_of_disjoint` | `[DecidableEq α] {s t} : Disjoint s t → (s ∪ t).card = s.card + t.card` |
| `Finset.exists_max_image` | `[LinearOrder α] (s : Finset β) (f : β → α) : s.Nonempty → ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x` |
| `Multiset.sort` | `(r := autoParam) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r] : Multiset α → List α` |
| `Nat.choose` | `ℕ → ℕ → ℕ` (binomial coefficient) |

`⚠ NOT FOUND` — `Finset.exists_le_image` (my guessed dual of `exists_max_image`)
does not exist; use `Finset.exists_min_image` for the min direction.
`Finset.card_union_eq_card_add_card_sub_card_inter` also does not exist; use
`Finset.card_union_add_card_inter` and rearrange with `Nat` subtraction lemmas
(or `Finset.card_union_of_disjoint` when disjoint).

---

## Quick-reference: the load-bearing names

- Euler parity (closed vs open tour): `SimpleGraph.Walk.IsEulerian.even_degree_iff`
  and `…IsEulerian.card_odd_degree` (0 or 2 odd-degree vertices).
- Hamilton cycle = `structure SimpleGraph.Walk.IsHamiltonianCycle extends p.IsCycle`
  with field `isHamiltonian_tail`; graph-level `SimpleGraph.IsHamiltonian`,
  `.mono`, `.connected`.
- Add-an-edge: `SimpleGraph.edge`, `edge_adj`, `card_edgeFinset_sup_edge`,
  `lt_sup_edge`, `sup_edge_of_adj`.
- Handshake: `sum_degrees_eq_twice_card_edges`, `even_card_odd_degree_vertices`.
- Bridge: `SimpleGraph.IsBridge`, `isBridge_iff`, `isBridge_iff_adj_and_forall_cycle_notMem`.
- `Fintype G.ConnectedComponent` is an available instance under
  `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`.

## Known gaps (`⚠ NOT FOUND — must be built`)

1. Euler's theorem forward direction (even degrees ⇒ Eulerian tour exists) — TODO in Mathlib.
2. Complete-graph / `⊤` / Dirac-type Hamilton-cycle EXISTENCE construction.
3. Single-edge degree-bump lemma (`degree` under `G ⊔ edge`).
4. Bridge removal ⇒ component count `+1`.
5. Component-count monotonicity `Fintype.card G.ConnectedComponent` under `G ≤ H`.
