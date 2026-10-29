# Proof Log — Bondy & Murty Ch. 4 (Euler Tours & Hamilton Cycles)

How each theorem of Chapter 4 was formalized, what was actually **closed**, and what
remains a documented `sorry` (and *why* — every open core is mapped to a specific
primitive that Mathlib does not provide).

Source paper (formatter output):
`papers/bondy-murty-ch4-euler-hamilton.md`. Lean toolchain
`leanprover/lean4:v4.25.0-rc2`, Mathlib pre-built.

## Pipeline used

1. **`lean-searcher`** — one pass, cached the exact Mathlib Euler/Hamilton API to
   `search_log.md` (every signature grep- or `#check`-verified). This is the
   load-bearing artifact: it fixed the exact names `IsEulerian.even_degree_iff`,
   `IsEulerian.card_filter_odd_degree`, `IsHamiltonian.mono`, the `IsHamiltonianCycle`
   structure shape, and the five *gaps* Mathlib does not fill (see bottom).
2. **`lean-orchestrator`** — wrote the backward-planned sorry-skeleton across four
   modules + `OUTLINE.md`. Built every *missing definition* as a real, compiling `def`
   (only `closure` / `IsClosureRun` / `IsFleuryTrail` / `IsBlock` are `sorry`-body
   skeletons, which is unavoidable — their recursion/predicate encoding is out of scope
   for a skeleton pass) and stated all 24 theorem leaves.
3. **`lean-prover`** — closed the 5 genuinely-fillable leaves (the forward halves that
   reduce to existing Mathlib) and left the SORRY-CORE leaves untouched.

## Files & build status

```
EulerHamilton/
  Defs.lean       -- missing primitives (8 real defs + 3 def-skeletons + 2 filled API lemmas)
  Euler.lean      -- §4.1: Thm 4.1, Cor 4.1, Thm 4.7, Ex 4.1.3–4.1.6
  Hamilton.lean   -- §4.2: Thm 4.2/4.3/4.4/Cor 4.4, Lem 4.4.1/4.4.2, Ex 4.2.1/4.2.3/4.2.9
  Chvatal.lean    -- §4.2 Hard (>80): Thm 4.5, Thm 4.6, Cor 4.6 (bound + extremal)
```

```bash
lake build TCSlib.GraphTheory.EulerHamilton.Defs \
           TCSlib.GraphTheory.EulerHamilton.Euler \
           TCSlib.GraphTheory.EulerHamilton.Hamilton \
           TCSlib.GraphTheory.EulerHamilton.Chvatal
# ⇒ Build completed successfully (7416 jobs). Zero errors; only `declaration uses 'sorry'` warnings.
```

**Status legend.** `CLOSED` = sorry-free. `PARTIAL` = one direction of an `↔`
proved, the other a documented `sorry`. `SORRY-CORE` = stated with a real signature,
proof deferred (new mathematics absent from Mathlib). `DEF-SKELETON` = a `def`/`Prop`
whose body is `sorry`.

| # | Item | Lean name | Status |
|---|---|---|---|
| — | graph-level Eulerian predicate | `IsEulerianGraph` | **CLOSED (def)** |
| — | component count ω | `omega` | **CLOSED (def)** |
| — | join `G ∨ H` on `V ⊕ W` | `join` | **CLOSED (def)** |
| — | disjoint union `G + H` | `disjointUnion` | **CLOSED (def)** |
| — | `C_{m,n}` | `Cmn` | **CLOSED (def)** |
| — | sorted degree sequence | `degreeSequence` | **CLOSED (def)** |
| — | `degreeSequence` length / sorted | `degreeSequence_length` / `_sorted` | **CLOSED (lemmas)** |
| — | degree-majorisation | `DegreeMajorised` | **CLOSED (def)** |
| — | 2-connected | `IsTwoConnected` | **CLOSED (def)** |
| — | closure `c(G)` / run / Fleury / block | `closure`, `IsClosureRun`, `IsFleuryTrail`, `IsBlock` | **DEF-SKELETON** |
| 4.1 | Euler ⇔ no odd degree | `euler_tour_iff_no_odd_degree` | **PARTIAL** (⇒ closed) |
| 4.1c | Euler trail ⇔ ≤ 2 odd | `euler_trail_iff_le_two_odd` | **PARTIAL** (⇒ closed) |
| 4.7 | Fleury correctness | `fleury_produces_euler_tour` | SORRY-CORE |
| 4.1.3 | blocks of eulerian are eulerian | `block_eulerian_of_eulerian` | SORRY-CORE |
| 4.1.4 | even deg ⇒ cycle decomposition | `even_degree_cycle_decomposition` | SORRY-CORE |
| 4.1.5 | 2k odd ⇒ k covering trails | `odd_vertices_trail_cover` | SORRY-CORE |
| 4.1.6 | extendable tour ⇔ `G−v` forest | `trail_extends_iff_forest` | SORRY-CORE |
| — | `K_n` (n≥3) hamiltonian | `top_isHamiltonian` | SORRY-CORE |
| 4.2 | ham ⇒ ω(G−S) ≤ \|S\| | `hamiltonian_toughness` | SORRY-CORE |
| 4.3 | Dirac | `dirac_hamiltonian` | SORRY-CORE |
| 4.4.1 | Bondy–Chvátal | `bondy_chvatal` | **PARTIAL** (⇒ closed) |
| 4.4.2 | closure well defined | `closure_well_defined` | SORRY-CORE |
| 4.4 | ham ⇔ closure ham | `hamiltonian_iff_closure_hamiltonian` | SORRY-CORE |
| 4.4c | complete closure ⇒ ham | `hamiltonian_of_closure_complete` | SORRY-CORE |
| 4.2.1 | non-2-conn ⇒ nonham | `nonhamiltonian_of_not_two_connected` | SORRY-CORE |
| 4.2.3 | ham path ⇒ ω ≤ \|S\|+1 | `hamiltonian_path_toughness` | SORRY-CORE |
| 4.2.9 | ν>2δ ⇒ path length ≥ 2δ | `long_path_of_min_degree` | SORRY-CORE |
| 4.5 | Chvátal degree condition | `chvatal_hamiltonian` | SORRY-CORE |
| 4.6 | Chvátal degree-majorisation | `chvatal_degree_majorised` | SORRY-CORE |
| 4.6c | Ore/Bondy edge bound | `ore_bondy_edge_bound` | SORRY-CORE |
| 4.6c | Ore/Bondy extremal graphs | `ore_bondy_extremal` | SORRY-CORE |

**Tally.** 8 definitions + 2 API lemmas + 3 theorem-directions **closed** (sorry-free);
3 theorems **partially** proved (one `↔` direction each); 21 theorem cores + 4
def-skeletons remain documented `sorry`.

---

# Definitions (`Defs.lean`)

All eight are genuine compiling defs. The carrier-type changers (`join`,
`disjointUnion`, `Cmn`) discharge real `symm`/`loopless` obligations — they mirror the
proven `SimpleGraph.sum` pattern: `Adj` by a `match` on `Sum.inl/inr`, `symm` by the
same structural match, `loopless` by `cases u <;> simp`.

- **`IsEulerianGraph G := ∃ u (p : G.Walk u u), p.IsEulerian`** — the graph-level
  Eulerian predicate Mathlib lacks (it has only the walk-level `Walk.IsEulerian`).
- **`omega G := Fintype.card G.ConnectedComponent`** — ω. The needed
  `Fintype G.ConnectedComponent` instance fires exactly under
  `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]` (found in `WalkCounting.lean`), so
  those instances are on the def.
- **`join` / `disjointUnion` : `SimpleGraph (V ⊕ W)`** — cross edges `True` vs `False`.
- **`Cmn m n := (⊤ : Fin m).join ((⊥ : Fin m).disjointUnion (⊤ : Fin (n-2m)))`** — the
  extremal graph `C_{m,n} = K_m ∨ (K_m^c + K_{n-2m})` on `Fin m ⊕ (Fin m ⊕ Fin (n-2m))`.
- **`degreeSequence G := (univ.val.map G.degree).sort (· ≤ ·) : List ℕ`** — sorted
  ascending. Two API lemmas were **closed** by the prover:
  - `degreeSequence_length : G.degreeSequence.length = Fintype.card V`
    — `unfold degreeSequence; rw [Multiset.length_sort, Multiset.card_map]; simp [Finset.card_univ]`.
  - `degreeSequence_sorted : G.degreeSequence.Sorted (· ≤ ·)`
    — `unfold degreeSequence; exact Multiset.sort_sorted _ _`.
- **`DegreeMajorised G H := card V = card W ∧ ∀ i, G.degreeSequence.getD i 0 ≤ H.degreeSequence.getD i 0`**
  — positional `≤` via the total accessor `getD _ 0` (out-of-range indices compare `0 ≤ 0`).
- **`IsTwoConnected G := 3 ≤ card V ∧ G.Connected ∧ ∀ w, (G.induce {w}ᶜ).Connected`**.

**Def-skeletons** (`sorry` bodies, by necessity):
`closure` (least fixpoint of degree-sum-≥ν edge additions; termination measure
`#edgeFinset ≤ C(ν,2)`), `IsClosureRun` (placeholder Prop for a maximal closure run,
used only to *state* Lem 4.4.2), `IsFleuryTrail` (greedy-rule predicate), and the local
`IsBlock` (needed only to *state* Ex 4.1.3).

---

# §4.1 Euler tours (`Euler.lean`)

## Theorem 4.1 — Euler ⇔ no odd degree — `euler_tour_iff_no_odd_degree` · **PARTIAL**
```lean
(hne : G.edgeSet.Nonempty) (hconn : G.Connected) :
  G.IsEulerianGraph ↔ ∀ v, Even (G.degree v)
```
**B&M idea.** (⇒) each internal visit of the tour consumes two incident edges ⇒ every
degree even. (⇐) minimal counterexample: min-degree ≥ 2 gives a closed trail `C`; take
`C` maximal; a component `G'` of `G − E(C)` has even degrees and fewer edges ⇒ Eulerian
by minimality; splice `C` with `C'` at a shared vertex ⇒ a longer closed trail,
contradiction.

**How it's done in Lean.**
- **⇒ CLOSED.** After `rintro ⟨u, p, hp⟩ v`, the tour is *closed* (`p : G.Walk u u`), so
  in `hp.even_degree_iff : Even (G.degree x) ↔ (u ≠ v_end → …)` the premise `u ≠ u` is
  false and every degree is even:
  `exact hp.even_degree_iff.mpr (fun h => absurd rfl h)`.
- **⇐ SORRY-CORE (#02).** The existence converse is the crux of the whole Euler section
  and is **absent from Mathlib** (its own file marks it a TODO). It needs
  *strong induction on `#edgeFinset`* plus a "min-degree ≥ 2 ⇒ a closed trail exists"
  lemma (B&M Ex 1.7.2, unproven in the repo) and closed-trail splicing via `Walk.append`.

## Corollary 4.1 — Euler trail ⇔ ≤ 2 odd — `euler_trail_iff_le_two_odd` · **PARTIAL**
```lean
(hconn : G.Connected) :
  (∃ u v (p : G.Walk u v), p.IsEulerian) ↔ (univ.filter fun v => Odd (G.degree v)).card ≤ 2
```
**B&M idea.** (⇒) an Euler trail has 0 or 2 odd-degree vertices. (⇐) 0 odd ⇒ Thm 4.1;
exactly 2 odd `u,v` ⇒ add edge `uv`, take the Euler tour of `G+uv`, delete its first dart.

**How it's done in Lean.**
- **⇒ CLOSED.** `Walk.IsEulerian.card_filter_odd_degree` gives the odd-degree count is
  `0 ∨ 2`; `omega` finishes `≤ 2`:
  `have h := hp.card_filter_odd_degree rfl; rcases h with h | h <;> omega`.
- **⇐ SORRY-CORE (#04).** Fully depends on Thm 4.1's converse (itself open), plus the
  add-edge / strip-first-dart surgery (`SimpleGraph.edge`, `card_edgeFinset_sup_edge`,
  `Walk.tail`).

## Theorem 4.7 — Fleury correctness — `fleury_produces_euler_tour` · **SORRY-CORE (#05)**
```lean
(hE : G.IsEulerianGraph) {u v} (p : G.Walk u v) (hp : IsFleuryTrail G p) : p.IsEulerian
```
**B&M idea.** The terminus has degree 0 in the untraced subgraph ⇒ the trail is closed;
if it were not an Euler tour, the last `[S, S̄]`-crossing edge would be a *forced* bridge
of an even-degree induced subgraph — impossible, since an even-degree graph has no bridge
(Ex 2.2.6a). **Blocked by:** the algorithm-shaped `IsFleuryTrail` predicate
(def-skeleton) and the missing "even-degree ⇒ no bridge" lemma.

## Exercises 4.1.3 – 4.1.6 · **SORRY-CORE (#06–#09)**
- **4.1.3** `block_eulerian_of_eulerian` — even degrees restrict to a block; blocked by
  the missing `IsBlock` predicate.
- **4.1.4** `even_degree_cycle_decomposition` — `∃` an edge-partitioning family of cycles;
  induction peeling one cycle at a time (needs the closed-trail-exists lemma).
- **4.1.5** `odd_vertices_trail_cover` — pair the `2k` odd vertices, add `k` edges, take an
  Euler tour, split it; depends on Thm 4.1 / Ex 4.1.4.
- **4.1.6** `trail_extends_iff_forest` — every trail from `v` extends to an Euler tour iff
  `G − v` is acyclic (`SimpleGraph.IsAcyclic`); both directions, depends on Thm 4.1.

---

# §4.2 Hamilton cycles (`Hamilton.lean`)

## `top_isHamiltonian` — `K_n` (n≥3) is hamiltonian · **SORRY-CORE (#10)**
```lean
(hν : 3 ≤ Fintype.card V) : (⊤ : SimpleGraph V).IsHamiltonian
```
**Idea.** Any cyclic ordering of the vertices is a Hamilton cycle. **Blocked by:** Mathlib
has **no** complete-graph Hamilton-cycle construction and no way to turn a `Fintype`
enumeration into an `IsHamiltonianCycle` (grep shows `IsHamiltonianCycle` is referenced
only inside `Hamiltonian.lean`; `cycleGraph` exists but has no `IsHamiltonianCycle`
lemma). This small lemma is the reusable prerequisite for Cor 4.4 and Dirac.

## Theorem 4.2 — toughness `ω(G−S) ≤ |S|` — `hamiltonian_toughness` · **SORRY-CORE (#11)**
```lean
(hG : G.IsHamiltonian) (S : Finset V) (hS : S.Nonempty) (hSne : S ≠ univ) :
  (G.induce (↑Sᶜ : Set V)).omega ≤ S.card
```
**B&M idea.** Deleting `|S|` vertices from a Hamilton cycle leaves ≤ `|S|` arcs, so
`ω(C − S) ≤ |S|`; `C − S` spans `G − S`, so `ω(G − S) ≤ ω(C − S)`. **Blocked by:**
component-count monotonicity `Fintype.card ConnectedComponent` under a spanning subgraph —
**not in Mathlib** — plus the cycle-arc count.

## Theorem 4.3 — Dirac — `dirac_hamiltonian` · **SORRY-CORE (#12)**
```lean
(hν : 3 ≤ Fintype.card V) (hδ : Fintype.card V ≤ 2 * G.minDegree) : G.IsHamiltonian
```
**B&M idea.** Maximal nonhamiltonian `G`; nonadjacent `u,v` give a Hamilton path
`v₁…v_ν`; `S = {vᵢ : u v_{i+1} ∈ E}` and `T = {vᵢ : vᵢ v ∈ E}` are disjoint and both miss
`v_ν`, forcing `d(u)+d(v) < ν`, contradicting `δ ≥ ν/2`. Stated multiplicatively
(`card V ≤ 2 * minDegree`) so `omega` can handle the arithmetic. **Blocked by:** the
`S,T` surgery (shared with Bondy–Chvátal) and graph maximality via well-founded recursion
on `#edgeFinset`. Cheapest route is as a corollary of Cor 4.4 once `closure` exists.

## Lemma 4.4.1 — Bondy–Chvátal — `bondy_chvatal` · **PARTIAL**
```lean
{u v} (huv : ¬ G.Adj u v) (hne : u ≠ v) (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
  G.IsHamiltonian ↔ (G ⊔ SimpleGraph.edge u v).IsHamiltonian
```
**B&M idea.** (⇒) adding an edge cannot destroy a Hamilton cycle. (⇐) if `G+uv` is
hamiltonian but `G` is not, the Hamilton cycle must use `uv`, giving a Hamilton *path* in
`G`; the `S,T` disjointness argument yields `d(u)+d(v) < ν`, contradiction.

**How it's done in Lean.**
- **⇒ CLOSED.** `G ≤ G ⊔ edge u v` is `le_sup_left`, and Hamiltonicity is monotone:
  `exact hG.mono le_sup_left`.
- **⇐ SORRY-CORE (#14).** The bespoke cycle surgery; it factors out the same `S,T` core
  as Dirac. Not in Mathlib.

## Lemma 4.4.2 — closure well defined — `closure_well_defined` · **SORRY-CORE (#15)**
```lean
(H₁ H₂ : SimpleGraph V) (h₁ : G.IsClosureRun H₁) (h₂ : G.IsClosureRun H₂) : H₁ = H₂
```
**B&M idea.** Newman-style confluence: the first edge `uv` added by run 1 but absent from
run 2 has, in its prefix, `d(u)+d(v) ≥ ν`; monotonicity carries this to the closed graph
of run 2, where `u,v` are nonadjacent — impossible in a closed graph. **Blocked by:** the
`closure` / `IsClosureRun` def-skeletons (chain-of-`SimpleGraph`s encoding + termination).

## Theorem 4.4 — ham ⇔ closure ham — `hamiltonian_iff_closure_hamiltonian` · **SORRY-CORE (#16)**
```lean
G.IsHamiltonian ↔ G.closure.IsHamiltonian
```
**B&M idea.** Apply Lemma 4.4.1 once per edge added in forming the closure. (The ⇒
direction would be a one-line `IsHamiltonian.mono` *once* `G ≤ G.closure` is available —
but `closure` is a skeleton, so even that is deferred.) **Blocked by:** `closure` +
Lem 4.4.1(⇐).

## Corollary 4.4 — complete closure ⇒ ham — `hamiltonian_of_closure_complete` · **SORRY-CORE (#17)**
```lean
(hν : 3 ≤ Fintype.card V) (hc : G.closure = (⊤ : SimpleGraph V)) : G.IsHamiltonian
```
**B&M idea.** `K_ν` is hamiltonian (`top_isHamiltonian`); `rw [hc]` then Thm 4.4.
**Blocked by:** `top_isHamiltonian` (#10) + Thm 4.4 (#16).

## Exercises 4.2.1 / 4.2.3 / 4.2.9 · **SORRY-CORE (#18–#20)**
- **4.2.1** `nonhamiltonian_of_not_two_connected` (grade 44, cheapest) — Hamiltonian ⇒
  2-connected. Uses `IsHamiltonian.connected` and a cut-vertex/component argument against
  the real `IsTwoConnected` def.
- **4.2.3** `hamiltonian_path_toughness` — `ω(G−S) ≤ |S|+1`; the path analogue of Thm 4.2.
- **4.2.9** `long_path_of_min_degree` — connected, `ν > 2δ` ⇒ a path of length ≥ `2δ`;
  extremal longest-path argument.

---

# §4.2 Hard items, grades 85/90/87 (`Chvatal.lean`) · all **SORRY-CORE**

**Statement adaptation (Thm 4.5).** The paper threads an abstract `dseq : Fin ν → ℕ` with
a `G.degreeSequence = dseq` link and `Fin`-index `by sorry` bound obligations — which
would leak a `sorry` into the *statement itself*. We instead phrase Chvátal's condition
directly on `G.degreeSequence : List ℕ` via the total `List.getD _ 0`, with a `1 ≤ m`
guard keeping the `d_{ν-m}` index in range. `d_m` (1-indexed) is `getD (m-1) 0`.

## Theorem 4.5 — Chvátal's condition — `chvatal_hamiltonian` (#21)
```lean
(hν : 3 ≤ Fintype.card V)
(hcond : ∀ m, 1 ≤ m → 2*m < Fintype.card V →
   ¬ (G.degreeSequence.getD (m-1) 0 ≤ m ∧
      G.degreeSequence.getD (Fintype.card V - m - 1) 0 < Fintype.card V - m)) :
  G.IsHamiltonian
```
**B&M idea.** Show `c(G)` is complete: otherwise pick a nonadjacent pair `u,v` in `c(G)`
of maximal degree sum `< ν`; the ≥ m vertices of degree ≤ m (`m = d'(u)`) and ≥ ν−m of
degree < ν−m transfer to `G` (spanning subgraph), giving `d_m ≤ m`, `d_{ν−m} < ν−m` with
`m < ν/2` — contradicting `hcond`. Then Cor 4.4. **Blocked by:** closure-completeness +
Cor 4.4.

## Theorem 4.6 — Chvátal degree-majorisation — `chvatal_degree_majorised` (#22)
```lean
(hν : 3 ≤ Fintype.card V) (hnh : ¬ G.IsHamiltonian) :
  ∃ m, 0 < m ∧ 2*m < Fintype.card V ∧ DegreeMajorised G (Cmn m (Fintype.card V))
```
**B&M idea.** Contrapositive of Thm 4.5 gives `m` with `d_m ≤ m`, `d_{ν−m} < ν−m`; then
`(dᵢ)` is majorised by `(m^m, (ν−m−1)^{ν−2m}, (ν−1)^m)`, the degree sequence of `C_{m,ν}`.
**Blocked by:** Thm 4.5 + computing `degreeSequence (Cmn m ν)`. The carrier-type change
(`Cmn` lives on `V ⊕ W`) is why comparison goes through `DegreeMajorised`
(cardinality-matched), never definitional equality — the grade-90 difficulty.

## Corollary 4.6 — Ore/Bondy edge bound — `ore_bondy_edge_bound` (#23)
```lean
(hν : 3 ≤ Fintype.card V) (hε : (Fintype.card V - 1).choose 2 + 1 < G.edgeFinset.card) :
  G.IsHamiltonian
```
**B&M idea.** By Thm 4.6, `ε(G) ≤ ε(C_{m,ν}) ≤ C(ν−1,2)+1`, contradicting `hε`.
**Blocked by:** Thm 4.6 + the edge-count of `Cmn` (binomial identity via `nlinarith`).

## Corollary 4.6 (extremal) — `ore_bondy_extremal` (#24)
```lean
(hν : 3 ≤ Fintype.card V) (hnh : ¬ G.IsHamiltonian)
(hε : G.edgeFinset.card = (Fintype.card V - 1).choose 2 + 1) :
  Nonempty (G ≃g Cmn 1 (Fintype.card V)) ∨ (Fintype.card V = 5 ∧ Nonempty (G ≃g Cmn 2 5))
```
**B&M idea.** Equality in the edge bound forces `m = 1` or `(m,ν) = (2,5)` and an identical
degree sequence, hence a graph isomorphism (`SimpleGraph.Iso`, `≃g`). **Blocked by:** the
equality analysis + a degree-sequence-forces-isomorphism lemma.

---

# Why the cores stay `sorry`: the five Mathlib gaps

Every open core reduces to one (or more) of the primitives the searcher confirmed are
**absent from Mathlib** (`search_log.md`, "Known gaps"):

1. **Euler forward existence** — "even degrees ⇒ an Euler tour exists" (an explicit TODO
   in Mathlib's `Trails.lean`). Blocks Thm 4.1(⇐), Cor 4.1(⇐), Ex 4.1.4/4.1.5/4.1.6.
2. **Complete-graph / Dirac Hamilton-cycle construction** — no `IsHamiltonianCycle` from a
   `Fintype`. Blocks `top_isHamiltonian`, Cor 4.4, Dirac.
3. **Single-edge degree bump** — `degree` under `G ⊔ edge`. Needed by Cor 4.1(⇐), the
   `S,T` surgery in Dirac / Bondy–Chvátal.
4. **Bridge removal ⇒ component count `+1`** — blocks Fleury (Thm 4.7) and the ω arguments.
5. **Component-count monotonicity** `Fintype.card ConnectedComponent` under `G ≤ H` — blocks
   Thm 4.2 and Ex 4.2.3.

Plus three **structural constructions** internal to this file: the `closure` fixpoint (+
termination + confluence, Lem 4.4.2), the `IsFleuryTrail` greedy predicate (Thm 4.7), and
the `IsBlock` predicate (Ex 4.1.3). These are Mathlib-PR-scale efforts, not skeleton fills,
which is why they are honestly left as documented `sorry`s rather than fabricated proofs.

# What is genuinely proven (sorry-free)

- **8 new definitions** compiling with real well-formedness proofs — including the three
  carrier-type-changing ones (`join`, `disjointUnion`, `Cmn`) that the formatter graded as
  the hardest part of Thm 4.6 / Cor 4.6.
- **`degreeSequence_length`, `degreeSequence_sorted`** — the degree-sequence API.
- **Thm 4.1 (⇒)**, **Cor 4.1 (⇒)**, **Lem 4.4.1 (⇒)** — the three forward halves that the
  formatter identified as reducible to Mathlib's Eulerian/Hamiltonian API, each a
  one-to-two-line proof against `IsEulerian.even_degree_iff`,
  `IsEulerian.card_filter_odd_degree`, and `IsHamiltonian.mono` respectively.
