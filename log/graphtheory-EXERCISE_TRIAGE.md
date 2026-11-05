# TCSlib / GraphTheory — Exercise Declaration Triage

Scope: every declaration in `TCSlib/GraphTheory/*.lean` whose docstring opens with a
Bondy & Murty **exercise** label (`**Exercise n.m.k**` or `Ex n.m.k`). **226** such
declarations across 11 modules. `Trees.lean` contains **no** exercise declarations —
all 14 of its items are numbered theorems/corollaries/definitions from the chapter
body, so it is out of scope for this pass.

**Pass 1 (triage) changed no code.** Pass 2 has since applied part of it — see
§G below for exactly what was implemented and what deliberately was not.

---

## 0. Evidence base (mechanically established, not assumed)

Three facts were measured over the whole repository before any judgement was made.
They apply to *every* entry below and are therefore stated once here.

### 0.1 Downstream code references: essentially zero

Repository-wide reference count over `TCSlib/**/*.lean` **with comments and docstrings
stripped** (block `/- … -/`, doc `/-- … -/`, module `/-! … -/`, and `--` line comments
blanked, preserving line numbers), excluding each declaration's own body:

| Declaration | Kind | Code references elsewhere |
|---|---|---|
| `hypercube` (Ex 1.2.10) | `def` | 5 (all in `GraphsAndSubgraphs.lean`) |
| `WinsFrom` (Ex 5.1.4) | `def` | 1 (in `Matchings.lean`) |
| **all other 224** | — | **0** |

So **no exercise *theorem* in this library is referenced by any Lean code anywhere.**
The two exceptions are both `def`s. This is not evidence that the statements are
useless — it is a direct consequence of §0.2.

Wherever an entry below says "downstream references: none in code", that claim was
searched, not assumed.

### 0.2 Proof status: 208 / 226 are `sorry`

Only **18** exercise declarations have a real proof:

`edgeCard_le_choose_two`, `iso_card_eq`, `nonempty_iso_iff`, `edgeCard_eq_choose_two_iff_top`,
`hypercube`, `hypercube_card_vertices`, `hypercube_bipartite`, `incMatrix_col_sum`,
`adjMatrix_sq_diag`, `exists_embedding_into_completeGraph`, `induce_completeGraph`,
`subgraph_bipartite`, `degree_bounds`, `lineGraph_card_vertices`, `exists_path_of_walk`,
`card_walks_length_eq_adjMatrix_pow`, `dist_triangle` (all `GraphsAndSubgraphs.lean`),
and `edgeCard_ge_of_kEdgeConnected` (`Connectivity.lean`).

Notably, **14 of those 18 are one-line wrappers around an existing Mathlib lemma** —
which is why the duplicate-detection axis carries so much weight in this triage.

### 0.3 The real dependency graph lives in prose

The intended dependency structure is recorded in docstrings, not in code: **176 / 226**
exercise declarations are cited by name/number in at least one *other* declaration's
docstring. Those citation counts are reported per entry as "prose-cited by …" and are
the primary positive evidence for `KEEP_CORE`, since code-level evidence does not yet
exist anywhere in the library.

### 0.4 Vacuous and undischargeable statements

A statement is **vacuous** if it quantifies over a `def … := sorry` (an opaque constant
about which nothing is provable), and **undischargeable** if it takes a hypothesis
`h : P` where `P` is a `Prop := sorry` (no caller can ever supply `h`). Both were
checked by reading the definitions:

| Supporting definition | Site | Status |
|---|---|---|
| `petersenGraph` | `EdgeColourings.lean:310` | `:= sorry` — **opaque** |
| `petersenGraph` | `EulerHamilton.lean:1915` | `:= sorry` — **opaque** |
| `petersenGraph` | `Matchings.lean:341` | honest (Kneser graph on 2-subsets of `Fin 5`) |
| `petersenGraph` | `PlanarGraphs.lean:525` | honest (same construction) |
| `hararyGraph` | `Connectivity.lean:1304` | `:= sorry` — **opaque** |
| `minArcsDestroyingDirectedPaths` | `Networks.lean:630` | `:= sorry`, all args `_`-ignored |
| `minVerticesDestroyingDirectedPaths` | `Networks.lean:649` | `:= sorry`, all args `_`-ignored |
| `maxSTVertexDisjointPaths` | `Networks.lean:702` | `:= sorry`, all args `_`-ignored |
| `minSTSeparator` | `Networks.lean:715` | `:= sorry`, all args `_`-ignored |
| `Network.IncPath.iota`, `Network.revisedFlow` | `Networks.lean:447, ~470` | `:= sorry` — **opaque** |
| `IsSpanningTree` | `CycleSpaceBondSpace.lean:550` | `Prop := sorry` — **undischargeable** |
| `IsBasisMatrixOfTree` / `IsBasisMatrixOfTree'` | `CycleSpaceBondSpace.lean:648, 668` | `Prop := sorry` |
| `IsConnectedDigraph` | `CycleSpaceBondSpace.lean:344` | `Prop := sorry` |
| `associatedDigraph_pathEquiv` | `DirectedGraphs.lean:2099` | `Equiv … := sorry` — **opaque bijection** |
| `cube` | `Matchings.lean:301` | `Adj` honest; `sorry` only in `symm`/`loopless` — **not vacuous** |
| `gridGraph` | `Matchings.lean:374` | `Adj` honest; `sorry` only in `symm`/`loopless` — **not vacuous** |

`petersenGraph` is defined **four times** in this library, twice opaquely and twice
honestly — see §D.1.

### 0.5 Decision rules actually applied

* `KEEP_CORE` — the statement is a named/attributed theorem, a structural
  characterisation, a sharp bound or threshold, or is prose-cited as a dependency of
  other declarations, **and** is not blocked by §0.4 and not a Mathlib duplicate.
* `GENERALIZE` — only where **the book's own statement is strictly stronger than the
  Lean transcription**, or where another declaration in this repo explicitly asks for
  the general form. No generalization was invented merely because a constant could be
  turned into a variable.
* `KEEP_EXAMPLE` — the mathematical role is witness / counterexample / sharpness
  certificate / concrete benchmark. Retained and built, but not core API: an
  automated prover retrieving it can only use it on goals about that same object.
* `DEFER` — blocked by §0.4, or the docstring itself records unresolved source
  fidelity.
* `DROP_FROM_LIBRARY` — the Lean statement is alpha-equivalent to an existing Mathlib
  lemma (the proof is literally `exact <mathlib-name>`), or restates a theorem already
  present locally. **The source record is retained** in the extraction archive.

Statements that are **false or under-hypothesised** are reported in §C, *separately*
from their retention recommendation, as instructed.

---

## A. Per-declaration classification

Format per entry: `Recommendation · Confidence · Role · Destination`, then evidence
(downstream / upstream / existing equivalent / constants), reasoning, fidelity.

---

## A.1 `GraphsAndSubgraphs.lean` — chapter 1 (38 declarations)

### Ex 1.1.3 — `edgeCard_le_choose_two` (L129, proved)
**DROP_FROM_LIBRARY · high · duplicate · ExtractionArchive**
- *Source:* "If `G` is simple, then `ε ≤ C(ν, 2)`."
- *Downstream:* no code refs; prose-cited by `edgeCard_eq_choose_two_iff_top`, `connected_of_edgeCard_gt`.
- *Upstream:* none local.
- *Existing equivalent:* **yes** — Mathlib `SimpleGraph.card_edgeFinset_le_card_choose_two`; the proof body is exactly that term.
- *Constants:* `2` is the arity of an edge, structural, not tunable.
- *Reasoning:* the declaration adds no statement content over the Mathlib lemma and no notation the book needs; the two prose citers can cite Mathlib directly.
- *Fidelity:* none.

### Ex 1.2.2(a) — `iso_card_eq` (L184, proved)
**DROP_FROM_LIBRARY · medium · duplicate · ExtractionArchive**
- *Source:* "If `G ≅ H` then `ν(G) = ν(H)` and `ε(G) = ε(H)`."
- *Downstream:* no code refs; prose-cited by `selfComplementary_card_mod_four`.
- *Existing equivalent:* **yes** — the conjunction of Mathlib `Fintype.card_congr f.toEquiv` and `Iso.card_edgeFinset_eq`; the proof is `⟨_, _⟩` of those two.
- *Constants:* none.
- *Reasoning:* a two-term conjunction of two Mathlib lemmas is a packaging convenience, not an inference step; `selfComplementary_card_mod_four` needs only the `ε` half.
- *Fidelity:* none.

### Ex 1.2.5 — `nonempty_iso_iff` (L207, proved)
**KEEP_CORE · medium · structural characterisation (bridge) · Core/**
- *Source:* "`G ≅ H` iff there is a bijection `θ` with `uv ∈ E(G) ↔ θu θv ∈ E(H)`."
- *Downstream:* no code refs, no prose citers.
- *Existing equivalent:* partial — Mathlib has `≃g` as a structure but no `Nonempty (G ≃g H) ↔ ∃ θ, …` bridge lemma.
- *Constants:* none.
- *Reasoning:* it converts a hand-built vertex bijection into Mathlib's `≃g`, which is the direction a prover needs when discharging "these two graphs are isomorphic" from a concrete map. That is a reusable inference step, not a restatement.
- *Fidelity:* none.

### Ex 1.2.7 — `edgeCard_eq_choose_two_iff_top` (L236, proved)
**KEEP_CORE · high · structural characterisation / sharp case · Core/**
- *Source:* "`ε = C(ν, 2)` iff `G` is complete."
- *Downstream:* no code refs; prose-cited by `edgeCard_le_choose_two`.
- *Upstream:* Mathlib `card_edgeFinset_top_eq_card_choose_two`, `edgeFinset_mono`.
- *Existing equivalent:* Mathlib has the `→ ⊤` computation but not the `iff`.
- *Constants:* `C(ν,2)` is the extremal value, not an example.
- *Reasoning:* this is the equality case of Ex 1.1.3 and characterises `⊤` by an edge count — an inference step usable in any extremal argument that has pinned `ε` exactly.
- *Fidelity:* none.

### Ex 1.2.8(a) — `completeBipartite_edgeCard` (L271, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "`ε(K_{m,n}) = mn`."
- *Downstream:* none in code; prose-cited by `bipartite_edgeCard_le` and by `IndependentSetsCliques.completeBipartite_triangle_free_extremal`.
- *Existing equivalent:* not found in Mathlib for `completeBipartiteGraph`.
- *Constants:* `m`, `n` are universally quantified — no fixed constants.
- *Reasoning:* a base edge-count for the standard extremal family; the Turán/Mantel sharpness witness in ch. 7 cannot be stated without it.
- *Fidelity:* none.

### Ex 1.2.8(b) — `bipartite_edgeCard_le` (L299, sorry)
**KEEP_CORE · high · sharp bound · Core/**
- *Source:* "If `G` is simple and bipartite, `ε ≤ ν²/4`."
- *Downstream:* prose-cited by `completeBipartite_edgeCard`, `IndependentSetsCliques.completeBipartite_triangle_free_extremal`.
- *Constants:* `4` in `4 * ε ≤ ν²` is the AM–GM constant and is **sharp** (equality at balanced `K_{n,n}`), not arbitrary.
- *Reasoning:* the bipartite half of Mantel's theorem, attained exactly; ch. 7's extremal chapter depends on it.
- *Fidelity:* bipartiteness rendered as `Colorable 2`, matching Mathlib's `IsBipartite`.

### Ex 1.2.10 — `hypercube` (L321, `def`, proved)
**KEEP_CORE · high · definition · Core/**
- *Source:* the `k`-cube: `k`-bit strings, adjacent iff differing in exactly one coordinate.
- *Downstream:* **5 code references** — the only exercise declaration with genuine code reuse.
- *Existing equivalent:* Mathlib has **no** named hypercube graph. But `Matchings.cube` (L301) is a second, independent definition of the same object with the same `Adj`.
- *Constants:* `k` is a parameter.
- *Reasoning:* a definition Mathlib lacks, with real in-repo use.
- *Fidelity:* faithful. ⚠ **Duplicated as `Matchings.cube`** — see §D.2.

### Ex 1.2.10 — `hypercube_card_vertices` (L333, proved)
**DROP_FROM_LIBRARY · high · duplicate/computation · ExtractionArchive**
- *Source:* "The `k`-cube has `2^k` vertices."
- *Downstream:* none in code.
- *Existing equivalent:* **yes** — the statement is `Fintype.card (Fin k → Bool) = 2 ^ k`, i.e. Mathlib's `Fintype.card_fun`; the proof is `by simp`.
- *Constants:* `2` is the alphabet size, structural.
- *Reasoning:* routine, Mathlib-immediate, and see fidelity.
- *Fidelity:* ⚠ **the statement never mentions `hypercube`.** It is a fact about the carrier type, not about the graph. A reader retrieving "the k-cube has 2^k vertices" gets a lemma with no graph in it.

### Ex 1.2.10 — `hypercube_edgeCard` (L356, sorry)
**KEEP_CORE · medium · reusable lemma · Core/**
- *Source:* "The `k`-cube has `k · 2^(k-1)` edges."
- *Downstream:* none in code; prose-cited within the hypercube family.
- *Constants:* `k`, `2` structural; the value is exact, not a bound.
- *Reasoning:* the proof route (`hypercube k` is `k`-regular, then handshake) produces the reusable `k`-regularity fact; the edge count itself is the standard reference value.
- *Fidelity:* `k - 1` is ℕ-subtraction; at `k = 0` both sides are `0`, so the statement is correct there.

### Ex 1.2.10 — `hypercube_bipartite` (L378, proved)
**KEEP_CORE · high · structural property · Core/**
- *Downstream:* none in code; the parity-colouring it establishes is what `Matchings.cube_isPerfectMatching` (Ex 5.1.1(a)) is built on.
- *Existing equivalent:* none in Mathlib.
- *Reasoning:* proved, non-trivial, and the entry point for every matching/colouring statement about cubes.
- *Fidelity:* none.

### Ex 1.2.11(b) — `selfComplementary_card_mod_four` (L430, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "If `G` is self-complementary, `ν ≡ 0` or `1 (mod 4)`."
- *Downstream:* prose-cited by `EulerHamilton.hamiltonian_path_of_self_complementary` (Ex 4.2.5).
- *Upstream:* Ex 1.2.2(a) (`ε(G) = ε(Gᶜ)`).
- *Constants:* `4` is forced by `2ε = C(ν,2)`; it is the modulus the arithmetic produces, not a choice.
- *Reasoning:* a classical necessary condition, and a cross-chapter dependency.
- *Fidelity:* none.

### Ex 1.3.1(a) — `incMatrix_col_sum` (L489, proved)
**DROP_FROM_LIBRARY · high · duplicate · ExtractionArchive**
- *Existing equivalent:* **yes** — proof is `G.sum_incMatrix_apply_of_mem_edgeSet he`, alpha-equivalent to the Mathlib lemma.
- *Downstream:* prose-cited by `sum_degrees_eq_two_mul_edgeCard`.
- *Fidelity:* the book's part (b) (column sums of the *adjacency* matrix) is not stated.

### Ex 1.5.2 — `adjMatrix_sq_diag` (L511, proved)
**GENERALIZE · high · reusable lemma · Core/**
- *Source:* "If `G` is simple, the diagonals of **both** `MMᵀ` and `A²` are the degrees."
- *Downstream:* prose-cited by `card_walks_length_eq_adjMatrix_pow`, and by `CycleSpaceBondSpace.lapMatrix_eq_orientedIncMatrix_mul_transpose`.
- *Existing equivalent:* the `A²` half is Mathlib's `adjMatrix_mul_self_apply_self` verbatim.
- *Constants:* `2` is the power, structural.
- *Reasoning:* as stated it is a pure Mathlib alias and would be a `DROP`. But the book states **two** claims and only one was transcribed; the missing `MMᵀ` half is *not* in Mathlib and is exactly the ch. 12 identity `C = MMᵀ` restricted to the diagonal. Generalizing recovers content rather than inventing it.
- *Fidelity:* ⚠ the `MMᵀ` half of the book's statement is absent.
- **Possible generalized form:** `(G.incMatrix ℕ * (G.incMatrix ℕ)ᵀ) v v = G.degree v ∧ (G.adjMatrix ℕ ^ 2) v v = G.degree v` — i.e. state both conjuncts the source states.

### Ex 1.4.1 — `exists_embedding_into_completeGraph` (L578, proved)
**DROP_FROM_LIBRARY · medium · duplicate · ExtractionArchive**
- *Source:* "Every simple graph on `n` vertices is isomorphic to a subgraph of `Kₙ`."
- *Existing equivalent:* the Lean statement is `G ≤ completeGraph V`, proved by `fun _ _ h => h.ne` — i.e. `le_top` for `SimpleGraph`.
- *Constants:* none.
- *Reasoning:* the transcription is so weak it is definitional; nothing downstream can use it that could not use `le_top`.
- *Fidelity:* ⚠ **materially weaker than the source.** The book quantifies over any simple graph on `n` vertices and asks for an isomorphism onto a subgraph of `Kₙ`; the Lean version fixes the carrier and asserts `≤ ⊤`. The docstring records that the original `↪g` form was *false* (Mathlib's `↪g` is an induced embedding) and was weakened; the weakening went past the point of content.

### Ex 1.4.2(a) — `induce_completeGraph` (L594, proved)
**KEEP_CORE · medium · reusable lemma · Core/**
- *Source:* "Every induced subgraph of a complete graph is complete."
- *Downstream:* prose-cited by `subgraph_bipartite`.
- *Existing equivalent:* no direct Mathlib `induce_top` was found.
- *Reasoning:* `(⊤ : SimpleGraph V).induce s = ⊤` is a rewriting lemma a prover will hit whenever it restricts to a vertex subset of a complete graph; small but genuinely reusable.
- *Fidelity:* none.

### Ex 1.4.2(b) — `subgraph_bipartite` (L615, proved)
**GENERALIZE · medium · structural special case · Core/**
- *Source:* "Every subgraph of a bipartite graph is bipartite."
- *Downstream:* prose-cited by `induce_completeGraph`.
- *Existing equivalent:* the spanning case is Mathlib's `Colorable.mono_left` verbatim.
- *Constants:* the `2` in `Colorable 2` is the definition of bipartite, essential.
- *Reasoning:* as stated it is a Mathlib alias restricted to `H ≤ G` on the *same carrier*. The book means all subgraphs, including induced ones on a smaller carrier, and the docstring says so explicitly. The general form is source-supported and is not a Mathlib alias.
- *Fidelity:* ⚠ the induced/different-carrier case, which is most of what "subgraph" means in B&M, is not covered.
- **Possible generalized form:** `∀ (s : Set V) (H : SimpleGraph V), H ≤ G → G.Colorable 2 → (H.induce s).Colorable 2` — spanning and induced together, i.e. the book's "subgraph".

### Ex 1.5.1 — `degree_bounds` (L707, proved)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "`δ ≤ 2ε/ν ≤ Δ`."
- *Downstream:* none found.
- *Existing equivalent:* Mathlib has `minDegree_le_degree` / `degree_le_maxDegree` and the handshake, but not the packaged average-degree sandwich.
- *Constants:* `2` is the handshake constant.
- *Reasoning:* the average-degree sandwich is the workhorse of every counting argument in chapters 1, 7 and 8; stated multiplicatively it avoids ℕ-division, so it is directly usable.
- *Fidelity:* stated as `ν·δ ≤ 2ε ≤ ν·Δ` to avoid division — a faithful rearrangement.

### Ex 1.5.3 — `regular_bipartite_card_eq` (L742, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "A `k`-regular bipartite graph with `k > 0` has `|X| = |Y|`."
- *Downstream:* none in code; the fact is used implicitly by Ex 5.2.3(a) and Ex 6.1.3(a).
- *Constants:* `hk : 0 < k` is **essential to the truth** — at `k = 0` any two disjoint sets form a bipartition of the edgeless graph.
- *Reasoning:* a double-counting structural lemma that every regular-bipartite argument opens with.
- *Fidelity:* uses Mathlib's explicit `IsBipartiteWith s t`; faithful.

### Ex 1.5.4 — `exists_two_same_degree` (L767, sorry)
**KEEP_EXAMPLE · medium · example (pigeonhole) · Examples/**
- *Source:* "In any group of two or more people, two have the same number of friends."
- *Downstream:* none in code or prose.
- *Constants:* `2 ≤ ν` is the minimal nontrivial case and is essential (`ν = 1` is a counterexample only vacuously; `ν = 0` fails).
- *Reasoning:* a self-contained pigeonhole puzzle with no identified reuse; it is a demonstration of the degree-sequence pigeonhole rather than an inference step other results take. Real value as a regression test for the `degree : V → Fin ν` argument.
- *Fidelity:* the social phrasing is rendered graph-theoretically, faithfully.

### Ex 1.5.8 — `exists_bipartite_spanning_subgraph` (L798, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* (starred) "Every loopless `G` contains a bipartite spanning subgraph `H` with `d_H(v) ≥ ½ d_G(v)`."
- *Downstream:* none yet.
- *Constants:* the factor `½` is sharp for the local greedy/max-cut argument.
- *Reasoning:* this is the local max-cut lemma; it is a genuine reusable existence theorem, not an exercise curiosity, and is the standard route to "every graph has a large bipartite subgraph".
- *Fidelity:* stated as `degree v ≤ 2 * (H.neighborSet v).ncard` to avoid halving — faithful.

### Ex 1.5.10(a) — `lineGraph_card_vertices` (L820, proved)
**DROP_FROM_LIBRARY · high · duplicate · ExtractionArchive**
- *Existing equivalent:* **yes** — the statement is `Fintype.card G.edgeSet = G.edgeFinset.card`, proved by `(Set.toFinset_card _).symm`.
- *Reasoning:* pure `Set`/`Finset` bookkeeping; contains no graph theory.
- *Fidelity:* none.

### Ex 1.5.10(a) — `lineGraph_edgeCard` (L844, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "`ε(L(G)) = ∑_v C(d(v), 2)`."
- *Downstream:* prose-cited by `lineGraph_card_vertices`.
- *Existing equivalent:* Mathlib has `lineGraph` but not its edge count.
- *Constants:* `2` in `choose 2` is structural.
- *Reasoning:* the only quantitative line-graph fact in the library; chapters 6 and 8 both reason about `L(G)` and need it.
- *Fidelity:* simplicity is load-bearing (two edges share at most one end) and is carried by the `SimpleGraph` type.

### Ex 1.6.1 — `exists_path_of_walk` (L915, proved)
**DROP_FROM_LIBRARY · high · duplicate · ExtractionArchive**
- *Existing equivalent:* **yes** — `SimpleGraph.Walk.toPath`; the proof is that term.
- *Downstream:* prose-cited by `dist_triangle`.
- *Reasoning:* an alias for a Mathlib constructor.
- *Fidelity:* none.

### Ex 1.6.2 — `card_walks_length_eq_adjMatrix_pow` (L933, proved)
**DROP_FROM_LIBRARY · high · duplicate · ExtractionArchive**
- *Existing equivalent:* **yes** — `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`, verbatim.
- *Downstream:* prose-cited by `adjMatrix_sq_diag` and by `DirectedGraphs.adjMatrix_pow_apply_eq_card_directedWalk`.
- *Reasoning:* alias. Note the **directed** analogue (Ex 10.1.8) is *not* in Mathlib and is kept.
- *Fidelity:* none.

### Ex 1.6.3 — `exists_path_length_of_minDegree` (L957, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "If `G` is simple and `δ ≥ k`, then `G` has a path of length `k`."
- *Downstream:* the **most-cited exercise in chapter 1** — prose-cited by `Trees.lean`, `EulerHamilton.long_path_of_order_gt_two_minDegree`, `DirectedGraphs.exists_directedPath_length_ge_maxMinDegree`, `exists_cycle_of_minDegree_ge_two`, `exists_long_cycle_of_minDegree`.
- *Constants:* `k` is a parameter; the bound is sharp at `K_{k+1}`.
- *Reasoning:* the longest-path extremal argument packaged once; four separate later results are written against it.
- *Fidelity:* none.

### Ex 1.6.4 — `connected_iff_forall_partition_edge` (L983, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "`G` is connected iff every partition of `V` into two nonempty parts has a crossing edge."
- *Downstream:* prose-cited by `connected_of_edgeCard_gt`.
- *Existing equivalent:* not found in Mathlib in this form.
- *Reasoning:* converts connectivity into a finite combinatorial condition — precisely the shape needed by counting proofs of connectivity (Ex 1.6.5(a) is one), and by every edge-cut argument in chapters 2 and 3.
- *Fidelity:* none.

### Ex 1.6.5(a) — `connected_of_edgeCard_gt` (L1008, sorry)
**KEEP_CORE · high · sharp threshold · Core/**
- *Source:* "If `G` is simple and `ε > C(ν-1, 2)`, then `G` is connected."
- *Downstream:* none yet.
- *Constants:* `C(ν-1,2)` is **sharp** — part (b) of the same exercise asks for the disconnected extremal graph attaining it (`K_{ν-1}` plus an isolated vertex).
- *Reasoning:* an extremal threshold, not a numeric accident.
- *Fidelity:* part (b) (the sharpness witness) is not stated; that is a gap, not an error.

### Ex 1.6.7 — `compl_connected_of_not_connected` (L1034, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "If `G` is disconnected, `Gᶜ` is connected."
- *Downstream:* none yet.
- *Reasoning:* a standard complement lemma that every "one of `G`, `Gᶜ` has property P" argument uses (Nordhaus–Gaddum in ch. 8 among them).
- *Fidelity:* `[Nonempty V]` is added and is needed.

### Ex 1.6.8(a) — `components_deleteEdge` (L1061, sorry)
**GENERALIZE · high · reusable lemma · Core/**
- *Source:* "If `e ∈ E`, then `ω(G) ≤ ω(G - e) ≤ ω(G) + 1`."
- *Downstream:* prose-cited by `Trees.tree_card_edgeFinset` and `Trees.connected_two_non_cutVertices`.
- *Constants:* the `+1` is exact and essential (deleting one edge splits at most one component).
- *Reasoning:* `Trees.lean`'s corollary 2.7 skeleton says, in its own words, that the monotonicity `H ≤ K → ω(K) ≤ ω(H)` "is used here and is worth a standalone lemma — chapter 1's exercise 1.6.8(a) needs the same fact." The generalization is therefore requested by the repository itself, not invented. Keep this exercise as the single-edge instance carrying the sharp `+1`.
- *Fidelity:* uses `Fintype.card ConnectedComponent` where `Trees.numComponents` uses `Nat.card` — see §D.3.
- **Possible generalized form:** `theorem numComponents_antitone {H K : SimpleGraph V} (h : H ≤ K) : K.numComponents ≤ H.numComponents`, with Ex 1.6.8(a) retained as the `K = G`, `H = G - e` instance plus the `≤ ω(G) + 1` half.

### Ex 1.6.11 — `dist_triangle` (L1086, proved)
**DROP_FROM_LIBRARY · high · duplicate · ExtractionArchive**
- *Existing equivalent:* **yes** — `SimpleGraph.Connected.dist_triangle`; the proof is `hc.dist_triangle`.
- *Fidelity:* ⚠ the name `SimpleGraph.dist_triangle` **shadows** the metric-space `dist_triangle` inside this namespace — see §D.4.

### Ex 1.6.12 — `compl_diam_lt_of_diam_gt` (L1113, sorry)
**KEEP_CORE · medium · sharp threshold · Core/**
- *Source:* "If `G` has diameter greater than three, `Gᶜ` has diameter less than three."
- *Downstream:* none yet.
- *Constants:* both `3`s are **sharp** — the statement fails if either is relaxed; this is the classical diameter dichotomy.
- *Reasoning:* the constants are a threshold, not example values, which is exactly the case the retention policy protects.
- *Fidelity:* ⚠ Mathlib's `diam` returns `0` for disconnected graphs, so the ℕ-valued reading of "diameter less than three" needs care; recorded in the docstring.

### Ex 1.6.14 — `exists_induced_path_of_connected_not_complete` (L1136, sorry)
**KEEP_CORE · high · bridge lemma · Core/**
- *Source:* "If `G` is simple, connected, not complete, there are `u,v,w` with `uv, vw ∈ E`, `uw ∉ E`."
- *Downstream:* prose-cited by `VertexColourings.brooks_chromaticNumber_le_maxDegree` — a direct dependency of Brooks' theorem.
- *Reasoning:* the standard entry point to Brooks; a genuine cross-chapter bridge lemma.
- *Fidelity:* none.

### Ex 1.7.1 — `edge_in_cycle_of_closed_trail` (L1228, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "If an edge lies in a closed trail, it lies in a cycle."
- *Downstream:* none yet, but it is the standard trail→cycle reduction ch. 4 needs.
- *Reasoning:* converts the weaker "closed trail" hypothesis into "cycle", which is what every cycle-based lemma consumes.
- *Fidelity:* ⚠ the docstring notes the walk analogue is false; the `IsTrail` hypothesis is load-bearing and present.

### Ex 1.7.2 — `exists_cycle_of_minDegree_ge_two` (L1250, sorry)
**KEEP_CORE · high · sharp threshold / reusable lemma · Core/**
- *Source:* "If `δ ≥ 2`, `G` contains a cycle."
- *Downstream:* prose-cited by `CycleSpaceBondSpace.exists_arcCycle_subset_support_of_isCirculation`, `EulerHamilton.euler_tour_iff_no_odd_degree`, `EulerHamilton.even_degree_cycle_decomposition`, `exists_long_cycle_of_minDegree`.
- *Constants:* `2` is a **sharp threshold** — `δ ≥ 1` permits forests.
- *Reasoning:* four downstream citers across three chapters; this is a core inference step.
- *Fidelity:* none.

### Ex 1.7.3 — `exists_long_cycle_of_minDegree` (L1271, sorry)
**KEEP_CORE · high · sharp bound · Core/**
- *Source:* (starred) "If `G` is simple with `δ ≥ 2`, `G` has a cycle of length ≥ `δ + 1`."
- *Downstream:* prose-cited by `DirectedGraphs.exists_directedCycle_length_ge`.
- *Constants:* `δ + 1` is **attained** by `K_{δ+1}` — sharp.
- *Reasoning:* strictly stronger than Ex 1.7.2 and separately cited; both are worth keeping.
- *Fidelity:* none.

### Ex 1.7.4(a) — `girth_four_regular_card_ge` (L1291, sorry)
**KEEP_CORE · high · sharp bound (Moore-type) · Core/**
- *Source:* "A `k`-regular graph of girth four has at least `2k` vertices."
- *Downstream:* prose-cited by `girth_five_regular_card_ge` and by `EulerHamilton.petersenGraph`.
- *Constants:* girth `= 4` is a **named structural class**; `2k` is **sharp**, attained uniquely by `K_{k,k}` (the book says so).
- *Reasoning:* the `g = 4` case of the Moore bound; the constants are extremal data.
- *Fidelity:* none.

### Ex 1.7.4(b) — `girth_five_regular_card_ge` (L1320, sorry)
**KEEP_CORE · high · sharp bound (Moore-type) · Core/**
- *Source:* "A `k`-regular graph of girth five has at least `k² + 1` vertices."
- *Downstream:* prose-cited by `girth_four_regular_card_ge`, `EulerHamilton.petersenGraph`.
- *Constants:* girth `= 5` is a named class; `k² + 1` is the Moore bound, attained at `k = 3` by the Petersen graph — the reason the Petersen graph recurs across this library.
- *Reasoning:* sharp, named, and cross-referenced.
- *Fidelity:* ⚠ `k - 1` ℕ-subtraction noted; `k = 0` degenerates harmlessly to `1 ≤ ν`.

### Ex 1.7.6(a) — `exists_cycle_of_edgeCard_ge` (L1346, sorry)
**KEEP_CORE · high · sharp threshold · Core/**
- *Source:* "If `ε ≥ ν`, `G` contains a cycle."
- *Downstream:* none yet.
- *Constants:* `ε ≥ ν` is **sharp** — forests have `ε = ν - ω ≤ ν - 1`.
- *Reasoning:* the acyclicity/edge-count threshold; a standard inference step.
- *Fidelity:* ⚠ **the statement is false for empty `V`** and needs `[Nonempty V]` — the docstring says so. See §C.

---

## A.2 `Connectivity.lean` — chapters 2–3 (6 declarations)

### Ex 2.3.1(a) — `exists_isVertexCut_singleton_of_isBridge` (L791, sorry)
**KEEP_CORE · high · bridge lemma · Core/**
- *Source:* "If `G` is connected with `ν ≥ 3` and has a cut edge, then `G` has a cut vertex."
- *Downstream:* prose-cited by `vertexConnectivity_le_deleteEdge_succ` and `vertexConnectivity_le_edgeConnectivity` — both core theorems of the chapter.
- *Constants:* `3 ≤ ν` is **essential to the truth**: `K₂` has a cut edge and no cut vertex.
- *Reasoning:* an explicit dependency of the chapter's main inequality `κ ≤ κ' ≤ δ`.
- *Fidelity:* the exercise's part (b) ("the converse is not necessarily true") is not stated.

### Ex 3.3.2 — `hararyGraph_conn_eq` (L1440, sorry)
**DEFER · high · sharpness witness · Deferred/**
- *Source:* "`κ(H_{m,n}) = κ'(H_{m,n}) = m`."
- *Downstream:* none.
- *Upstream:* `hararyGraph` (`Connectivity.lean:1304`) is **`:= sorry`** — the statement is vacuous.
- *Constants:* `m` is a parameter; the value `m` is the extremal one (Harary graphs are the minimum-edge `m`-connected graphs).
- *Reasoning:* genuinely valuable — it certifies Theorem 3.3's sharpness — but nothing can be proved about an opaque graph. Blocked strictly on the definition.
- *Fidelity:* faithful once `hararyGraph` exists.

### Ex 3.1.2 — `edgeCard_ge_of_kEdgeConnected` (L1480, **proved**)
**KEEP_CORE · high · reusable bound · Core/**
- *Source:* "If `G` is `k`-edge-connected, `ε ≥ kν/2`."
- *Downstream:* none yet.
- *Existing equivalent:* none in Mathlib.
- *Constants:* `2` is the handshake constant; the bound is sharp for `k`-regular `k`-edge-connected graphs.
- *Reasoning:* one of only 18 proved exercises, stated multiplicatively (`kν ≤ 2ε`) so it is directly usable by `omega`/`linarith`.
- *Fidelity:* none.

### Ex 3.1.3(a) — `vertexConnectivity_eq_minDegree_of_delta_ge` (L1532, sorry)
**KEEP_CORE · high · sharp threshold · Core/**
- *Source:* "If `G` is simple and `δ ≥ ν - 2`, then `κ = δ`."
- *Downstream:* none yet.
- *Constants:* `ν - 2` is **exactly sharp** — part (b) of the same exercise asks for a graph with `δ = ν - 3` and `κ < δ`.
- *Reasoning:* a threshold theorem, and one of the few conditions under which the general inequality `κ ≤ δ` is forced to equality.
- *Fidelity:* part (b) (the sharpness witness) is not stated.

### Ex 3.1.6 — `vertexConn_eq_edgeConn_of_threeRegular` (L1571, sorry)
**KEEP_CORE · high · structural special case · Core/**
- *Source:* "If `G` is simple and 3-regular, `κ = κ'`."
- *Downstream:* none yet.
- *Constants:* `3` denotes the **named structural class of cubic graphs**; the statement is false for general `k`-regular graphs, so the constant is essential, not an example value.
- *Reasoning:* exactly the case the retention policy protects — a fixed constant naming a class.
- *Fidelity:* none.

### Ex 3.2.1 — `two_edge_connected_iff_two_edge_disjoint_paths` (L1615, sorry)
**KEEP_CORE · high · base case / bridge lemma · Core/**
- *Source:* "`G` is 2-edge-connected iff any two vertices are joined by two edge-disjoint paths."
- *Downstream:* prose-cited by `DirectedGraphs.robbins_orientation` and `Networks.k_edge_connected_iff_edge_disjoint_paths`.
- *Existing equivalent:* the general `k` form **does exist locally** as `Networks.k_edge_connected_iff_edge_disjoint_paths` (Menger).
- *Constants:* `2` is the base case of Menger's edge form.
- *Reasoning:* although subsumed by the general Menger statement, it is separately cited by Robbins' theorem, which needs only `k = 2` and is proved in a module that does not import `Networks.lean`. That is a real dependency, not redundancy.
- *Fidelity:* none.

---

## A.3 `EulerHamilton.lean` — chapter 4 (16 declarations)

### Ex 4.1.2 — `exists_eulerian_even_order_odd_size` (L1205, sorry)
**KEEP_EXAMPLE · high · example (witness) · Examples/**
- *Source:* "If possible, draw an eulerian graph with `ν` even and `ε` odd; otherwise explain why none exists."
- *Downstream:* none.
- *Constants:* none fixed — the statement existentially quantifies `n` and `G`.
- *Reasoning:* the content is exhibiting one graph; nothing can apply it as an inference step. Good regression test that the `IsEulerianGraph` predicate is satisfiable with the stated parities.
- *Fidelity:* the book's "otherwise explain why" branch is resolved in favour of existence by the Lean statement — a decision the transcription makes silently.

### Ex 4.1.4 — `even_degree_cycle_decomposition` (L1250, sorry)
**KEEP_CORE · high · reusable structure theorem · Core/**
- *Source:* "If `G` has no vertices of odd degree, `E(G)` partitions into edge-disjoint cycles."
- *Downstream:* prose-cited by `odd_vertices_trail_cover`.
- *Upstream:* Ex 1.7.2 (`exists_cycle_of_minDegree_ge_two`).
- *Reasoning:* Veblen's theorem — the structural core of Euler theory and of 2-factorisation (Ex 5.2.3(b) depends on the same idea).
- *Fidelity:* none.

### Ex 4.1.5 — `odd_vertices_trail_cover` (L1295, sorry)
**KEEP_CORE · high · reusable structure theorem · Core/**
- *Source:* "A connected `G` with `2k > 0` odd-degree vertices has `k` edge-disjoint trails covering `E`."
- *Downstream:* prose-cited by `even_degree_cycle_decomposition`.
- *Constants:* `2k` — the count is even by handshaking; `k` is the exact (sharp) number of trails.
- *Reasoning:* the general form of the Euler theorem; the standard "open Chinese postman" decomposition.
- *Fidelity:* none.

### Ex 4.1.6 — `ore_extendable_tour_iff_forest` (L1354, sorry)
**DEFER · high · unresolved fidelity · Deferred/**
- *Source:* (starred, Ore) "Let `G` be nontrivial and eulerian… every trail from `v` extends to an Euler tour iff `G - v` is a forest."
- *Downstream:* none.
- *Reasoning:* the docstring states outright: "⚠ **The statement is false as written.** The book's hypotheses 'nontrivial and eulerian' [are missing]". A statement known to be false cannot be classified for retention until repaired.
- *Fidelity:* ⚠ missing `Nontrivial` and `IsEulerianGraph` hypotheses. See §C.

### Ex 4.2.1(a) — `nonhamiltonian_of_not_two_connected` (L1405, sorry)
**KEEP_CORE · high · reusable lemma (certificate) · Core/**
- *Source:* "If `G` is not 2-connected, `G` is nonhamiltonian."
- *Downstream:* prose-cited 5× incl. `chvatal_bipartite_hamiltonian` and `Matchings.mutilated_chessboard`.
- *Constants:* `2` is the exact connectivity threshold a Hamilton cycle forces; `3 ≤ ν` is needed since Mathlib's Hamilton cycle requires length ≥ 3.
- *Reasoning:* the primary negative certificate for hamiltonicity, cited across two chapters.
- *Fidelity:* none.

### Ex 4.2.1(b) — `nonhamiltonian_of_unbalanced_bipartite` (L1451, sorry)
**KEEP_CORE · high · reusable lemma (certificate) · Core/**
- *Source:* "If `G` is bipartite with `|X| ≠ |Y|`, `G` is nonhamiltonian."
- *Downstream:* prose-cited 5×, including `Matchings.mutilated_chessboard` (Ex 5.2.1), which is essentially an application of it.
- *Reasoning:* the parity certificate; the mutilated-chessboard example is unprovable without it.
- *Fidelity:* none.

### Ex 4.2.3 — `hamiltonian_path_toughness` (L1490, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "If `G` has a Hamilton path, then `ω(G - S) ≤ |S| + 1` for every proper `S ⊆ V`."
- *Downstream:* none yet.
- *Constants:* the `+1` distinguishes the path condition from the cycle condition `ω(G-S) ≤ |S|` — essential.
- *Reasoning:* the toughness necessary condition, the general form of which subsumes 4.2.1(a); a standard reusable obstruction.
- *Fidelity:* none.

### Ex 4.2.4 — `chvatal_hamiltonian_path` (L1535, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (starred, Chvátal) degree-sequence condition for a Hamilton path.
- *Downstream:* none yet.
- *Constants:* `(ν+1)/2` is Chvátal's threshold, from the source.
- *Reasoning:* an attributed theorem and the sharpest classical degree-sequence sufficient condition.
- *Fidelity:* the degree-sequence condition is re-expressed via `filter` cardinalities rather than a sorted sequence; equivalent but not a literal transcription.

### Ex 4.2.5 — `hamiltonian_path_of_self_complementary` (L1584, sorry)
**GENERALIZE · medium · corollary · Core/**
- *Source:* "(a) if `d_m ≥ d'_m` for all `m ≤ ν/2` then `G` has a Hamilton path; (b) deduce that a self-complementary graph has a Hamilton path." (Clapham)
- *Downstream:* none yet.
- *Upstream:* Ex 1.2.11(b).
- *Reasoning:* only part (b) is stated; the docstring notes the proof "must either prove [part (a)] inline" — i.e. the general theorem is a hidden prerequisite. Part (a) is stated verbatim in the source, so stating it is transcription, not invention, and it is the reusable half.
- *Fidelity:* ⚠ part (a) is absent from the file although part (b) is deduced from it.
- **Possible generalized form:** state Ex 4.2.5(a) — `(∀ m, 2*m ≤ ν → d'_m ≤ d_m) → ∃ Hamilton path` — and derive the self-complementary case as a corollary.

### Ex 4.2.6 — `chvatal_bipartite_hamiltonian` (L1635, sorry)
**DEFER · high · unresolved fidelity · Deferred/**
- *Source:* (starred, Chvátal) bipartite degree-sequence condition.
- *Reasoning:* the docstring states "⚠ **The Lean statement below is best-effort and does not faithfully match the** [book's]". Retention cannot be decided against a statement that does not yet say what the source says.
- *Fidelity:* ⚠ admitted mismatch. See §C.

### Ex 4.2.8 — `erdos_hamiltonian` (L1681, sorry)
**KEEP_CORE · high · named theorem / sharp threshold · Core/**
- *Source:* (Erdős) "`ν ≥ 6δ` and `ε > C(ν-δ,2) + δ²` ⇒ hamiltonian."
- *Downstream:* none yet.
- *Constants:* `6` and the exact edge threshold are Erdős's, taken from the source; the threshold is sharp.
- *Reasoning:* an attributed extremal theorem with a sharp edge bound.
- *Fidelity:* none.

### Ex 4.2.9 — `long_path_of_order_gt_two_minDegree` (L1726, sorry)
**KEEP_CORE · high · named theorem / reusable lemma · Core/**
- *Source:* (starred, Dirac) "connected with `ν > 2δ` ⇒ a path of length ≥ `2δ`."
- *Downstream:* prose-cited by `nash_williams_regular_hamiltonian`.
- *Constants:* `2δ` is sharp.
- *Reasoning:* attributed, sharp, and an in-file dependency.
- *Fidelity:* none.

### Ex 4.2.10 — `nash_williams_regular_hamiltonian` (L1771, sorry)
**KEEP_CORE · medium · named theorem · Core/**
- *Source:* (Nash-Williams) "every `2k`-regular simple graph on `4k+1` vertices is hamiltonian (`k ≥ 1`)."
- *Downstream:* prose-cited by `long_path_of_order_gt_two_minDegree`.
- *Constants:* `2k` and `4k+1` are the exact extremal relation — this is a boundary case of Dirac's condition (`δ = 2k`, `ν = 4k+1`, so `δ` is one short of `ν/2`), not an arbitrary instance.
- *Reasoning:* attributed and structurally sharp; a legitimate core entry.
- *Fidelity:* ⚠ **the book's `k ≥ 1` is omitted and the statement is false at `k = 0`** (a one-vertex graph is not hamiltonian in Mathlib). Also blocked on an unproved parenthetical remark of the source. See §C.

### Ex 4.2.11(a) — `hamiltonConnected_edge_bound` (L1818, sorry)
**KEEP_CORE · high · sharp bound · Core/**
- *Source:* "If `G` is Hamilton-connected and `ν ≥ 4`, then `ε ≥ ⌈(3ν+1)/2⌉`."
- *Downstream:* prose-cited by `exists_extremal_hamiltonConnected`.
- *Constants:* `(3ν+1)/2` is **attained** — part (b) constructs the extremal graph. Sharp.
- *Reasoning:* an extremal lower bound with an explicit matching construction; textbook core.
- *Fidelity:* ⚠ **the book's `ν ≥ 4` is omitted and the statement is false at `ν = 3`.** See §C.

### Ex 4.2.11(b) — `exists_extremal_hamiltonConnected` (L1866, sorry)
**KEEP_EXAMPLE · high · sharpness witness · Examples/**
- *Source:* (starred, Moon) "For `ν ≥ 4`, construct a Hamilton-connected `G` with `ε = ⌈(3ν+1)/2⌉`."
- *Downstream:* prose-cited by `hamiltonConnected_edge_bound`.
- *Constants:* the edge count is the extremal value from part (a).
- *Reasoning:* its role is to certify that (a) is sharp. Valuable and must not be deleted, but it is a construction about one family, so it is not a retrievable inference step for general goals.
- *Fidelity:* ⚠ hypothesis is `3 ≤ ν`, the book requires `4 ≤ ν`. See §C.

### Ex 4.2.12 — `petersen_isHypohamiltonian` (L1957, sorry)
**DEFER · high · counterexample (blocked) · Deferred/**
- *Source:* "Show the Petersen graph is hypohamiltonian."
- *Downstream:* prose-cited by `IsHypohamiltonian`, `petersenGraph`.
- *Upstream:* `petersenGraph` in **this file** (`EulerHamilton.lean:1915`) is `:= sorry` — the statement quantifies over an opaque constant and asserts nothing.
- *Constants:* the Petersen graph is the canonical smallest hypohamiltonian graph — a named object, not an example value.
- *Reasoning:* mathematically a first-class counterexample, but currently vacuous. Unblocking is mechanical: an honest definition of the same graph already exists at `Matchings.lean:341` and `PlanarGraphs.lean:525`. See §D.1.
- *Fidelity:* faithful once the definition is real.

---

## A.4 `Matchings.lean` — chapter 5 (28 declarations)

### Ex 5.1.1(a) — `cube_isPerfectMatching` (L1130, sorry)
**KEEP_CORE · medium · structural special case · Core/**
- *Source:* "Every `k`-cube has a perfect matching (`k ≥ 2`)."
- *Downstream:* prose-cited within the matching-count family.
- *Upstream:* `cube` (honest `Adj`; `sorry` only in `symm`/`loopless`), Ex 1.2.10.
- *Constants:* ⚠ `2 ≤ k` is **stronger than necessary** — the docstring notes `1 ≤ k` suffices for the argument. So `2` here is neither sharp nor essential.
- *Reasoning:* a parameterised family theorem (not a single object), reusable for any cube-indexed construction.
- *Fidelity:* hypothesis stronger than the mathematics requires; see §C.

### Ex 5.1.1(b) — `card_perfectMatching_completeGraph` (L1170, sorry)
**KEEP_CORE · medium · reusable computation · Core/**
- *Source:* "Find the number of perfect matchings in `K_{2n}`."
- *Downstream:* prose-cited within the family.
- *Constants:* `(2n)!/(2ⁿ n!)` is the exact double-factorial count.
- *Reasoning:* a standard enumerative value that later counting arguments quote.
- *Fidelity:* ⚠ uses **natural-number division**; exact here, but the statement's truth depends on divisibility that the reader must verify. Recorded in the docstring.

### Ex 5.1.1(b) — `card_perfectMatching_completeBipartite` (L1208, sorry)
**KEEP_CORE · medium · reusable computation · Core/**
- *Source:* same exercise, `K_{n,n}` half.
- *Constants:* `n!` exact.
- *Reasoning:* cleaner than the `K_{2n}` half (no division) and equally standard.
- *Fidelity:* none.

### Ex 5.1.2 — `isTree_subsingleton_perfectMatching` (L1249, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "A tree has at most one perfect matching."
- *Downstream:* prose-cited by `isTree_perfectMatching_iff` (Ex 5.3.3).
- *Reasoning:* uniqueness results are exactly the reusable kind — any argument that produces a tree matching can immediately conclude it is *the* matching.
- *Fidelity:* ⚠ the induction leaves a forest, not a tree; the docstring flags that the statement should probably be proved for forests. Not an error in the statement.

### Ex 5.1.3 — `exists_regular_matchingFree` (L1293, sorry)
**KEEP_EXAMPLE · high · counterexample · Examples/**
- *Source:* "For each `k > 1`, find a `k`-regular simple graph with no perfect matching."
- *Downstream:* none.
- *Constants:* `k > 1` — `k = 1` would be a perfect matching itself, so the bound is essential.
- *Reasoning:* its purpose is to show regularity alone does not force a perfect matching, i.e. that Tutte's condition is needed. A counterexample family, not an inference step.
- *Fidelity:* none.

### Ex 5.1.4 — `WinsFrom` (L1329, `def`, sorry in termination)
**DEFER · high · unfinished construction · Deferred/**
- *Source:* the alternating vertex-selection game.
- *Downstream:* **1 code reference** (`first_player_wins_iff_no_perfect_matching`).
- *Reasoning:* the docstring records that the `sorry` here is in the **termination proof**, a third kind distinct from a missing theorem proof. Until termination is discharged the definition is not usable.
- *Fidelity:* faithful in intent.

### Ex 5.1.4 — `first_player_wins_iff_no_perfect_matching` (L1377, sorry)
**DEFER · high · blocked · Deferred/**
- *Source:* "The first player has a winning strategy iff `G` has no perfect matching."
- *Upstream:* `WinsFrom` (deferred above).
- *Reasoning:* a genuinely nice game-theoretic characterisation of perfect matchings, blocked on its own definition.
- *Fidelity:* ⚠ "the first player has a winning strategy" is rendered `∃ v₀, ¬ WinsFrom G {v₀} v₀`; the docstring flags this reading. See §C.

### Ex 5.1.5(a)(i) — `completeBipartite_one_factorable` (L1416, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* (starred) "`K_{n,n}` and `K_{2n}` are 1-factorable."
- *Downstream:* **prose-cited 11× — the most-cited exercise in the library**, including four declarations in `EdgeColourings.lean`.
- *Reasoning:* 1-factorability of the complete bipartite family is the combinatorial content behind `χ'(K_{n,n}) = Δ`; chapter 6 is written against it.
- *Fidelity:* ⚠ the `ZMod n` construction has to be transported to the `Fin n` carrier — a formalisation cost, not a fidelity gap.

### Ex 5.1.5(a)(i) — `completeGraph_even_one_factorable` (L1459, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* same exercise, `K_{2n}` half.
- *Downstream:* prose-cited 11×; the round-robin decomposition is the base of `χ'(K_{2n}) = 2n - 1` (Ex 6.2.1).
- *Constants:* `2n` — evenness is **essential**; `K_{2n+1}` is *not* 1-factorable.
- *Reasoning:* separately cited from the bipartite half and used by a different chapter-6 result.
- *Fidelity:* none.

### Ex 5.1.5(a)(ii) — `petersenGraph_not_one_factorable` (L1504, sorry)
**KEEP_EXAMPLE · high · counterexample · Examples/**
- *Source:* "The Petersen graph is not 1-factorable."
- *Downstream:* prose-cited 11×, including `EdgeColourings.petersenGraph_edgeChromaticNumber` (Ex 6.1.2), which is *deduced from it*.
- *Upstream:* `Matchings.petersenGraph` — **honest** here (Kneser graph on 2-subsets of `Fin 5`), so this statement is **not** vacuous.
- *Constants:* the Petersen graph is a named canonical object.
- *Reasoning:* the standard witness that cubic graphs can be class 2. It is a real downstream dependency and must be retained — but as a fact about one graph it is not a general inference step, so it belongs with the examples, not the core API.
- *Fidelity:* none.

### Ex 5.1.5(c) — `exists_three_factor_of_minDegree` (L1547, sorry)
**KEEP_CORE · high · reusable theorem · Core/**
- *Source:* "`ν` even and `δ ≥ ν/2 + 1` ⇒ `G` has a 3-factor" (via Dirac).
- *Downstream:* prose-cited 11× within the factorisation family.
- *Constants:* `ν/2 + 1` is one above Dirac's threshold — the `+1` is what buys the extra factor, so it is essential.
- *Reasoning:* a genuine factorisation theorem; the blocker is a **missing import** (`EulerHamilton.lean` is not imported here), not a missing definition, so it is not `DEFER`.
- *Fidelity:* stated as `ν + 2 ≤ 2δ` to avoid ℕ-division — faithful.

### Ex 5.1.6 — `completeGraph_odd_two_factorable` (L1595, sorry)
**KEEP_CORE · high · reusable decomposition theorem · Core/**
- *Source:* (starred) "`K_{2n+1}` is the union of `n` connected 2-factors (`n ≥ 1`)."
- *Downstream:* none yet.
- *Constants:* `2n+1` odd is **essential** (the even case decomposes differently), `n` is the exact number of factors.
- *Reasoning:* the odd complement of Ex 5.1.5(a)(i); together they cover the complete-graph factorisation story.
- *Fidelity:* the decomposition is spelled out inline instead of via `IsKFactorable` — noted, harmless.

### Ex 5.2.1 — `mutilated_chessboard` (L1642, sorry)
**KEEP_EXAMPLE · high · counterexample / benchmark · Examples/**
- *Source:* "`1×2` rectangles cannot tile an `8×8` board with two opposite corners removed."
- *Downstream:* none.
- *Upstream:* `gridGraph` (honest `Adj`), Ex 4.2.1(b).
- *Constants:* `8`, `8`, and the two corner squares are **the classic instance**, not arbitrary — the argument is the colouring/parity argument that Ex 4.2.1(b) supplies, and the `8×8` board is the canonical statement of it.
- *Reasoning:* a famous benchmark problem; it exercises the bipartite-imbalance certificate end to end. No general inference step.
- *Fidelity:* ⚠ requires "a bipartite graph with unequal sides has no perfect matching", which the docstring notes **does not exist in this file**.

### Ex 5.2.2(a) — `bipartite_perfectMatching_iff` (L1683, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "A bipartite `G` has a perfect matching iff `|N(S)| ≥ |S|` for all `S ⊆ V`."
- *Downstream:* prose-cited by Ex 5.2.2(b).
- *Existing equivalent:* Mathlib has Hall's marriage theorem for `Finset` families; this is the graph-side statement over all of `V`.
- *Reasoning:* Hall's condition as a decidable criterion is the single most retrievable matching fact.
- *Fidelity:* ⚠ `hcov : X ∪ Y = Set.univ` is **required** and has no counterpart in the book's statement (Mathlib's `IsBipartiteWith` does not force the parts to cover `V`). A real added hypothesis; see §C.

### Ex 5.2.2(b) — `exists_not_bipartite_hall_counterexample` (L1725, sorry)
**KEEP_EXAMPLE · high · counterexample · Examples/**
- *Source:* "Give an example showing the statement fails without bipartiteness."
- *Downstream:* prose-cited by Ex 5.2.2(a).
- *Reasoning:* precisely the kind of result the retention policy protects — it certifies that the `hbip` hypothesis of (a) cannot be dropped.
- *Fidelity:* ⚠ `Set.ncard` is not decidable as stated; noted in the docstring.

### Ex 5.2.3(a) — `regular_bipartite_one_factorable` (L1768, sorry)
**KEEP_CORE · high · reusable theorem · Core/**
- *Source:* "For `k > 0`, every `k`-regular bipartite graph is 1-factorable."
- *Downstream:* prose-cited by `EdgeColourings.edgeChromaticNumber_eq_maxDegree_of_isBipartite` (the alternative proof of Theorem 6.1) and `EdgeColourings.exists_regular_bipartite_supergraph`.
- *Constants:* `0 < k` needed only to exclude the degenerate empty decomposition.
- *Reasoning:* a named classical theorem and an explicit cross-chapter dependency of König's edge-colouring theorem.
- *Fidelity:* none.

### Ex 5.2.3(b) — `regular_two_factorable` (L1809, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (starred, Petersen) "every `2k`-regular graph is 2-factorable."
- *Downstream:* prose-cited within the factorisation family.
- *Constants:* `2k` even regularity is **essential** — odd-regular graphs are not 2-factorable.
- *Reasoning:* Petersen's 2-factor theorem, attributed and classical.
- *Fidelity:* none.

### Ex 5.2.4 — `exists_sdr` (L1856, sorry)
**DROP_FROM_LIBRARY · medium · duplicate · ExtractionArchive**
- *Source:* (P. Hall) systems of distinct representatives.
- *Downstream:* none.
- *Existing equivalent:* **yes** — the docstring itself says "**WRAPPER of Mathlib's Hall**… This is a one-liner", and the statement `(∃ f, Injective f ∧ ∀ i, f i ∈ A i) ↔ ∀ J, J.card ≤ (J.biUnion A).card` is Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective` up to argument order.
- *Reasoning:* an alias. **Flagged for human review** (§E): the SDR *phrasing* is a distinct retrieval surface from the graph phrasing, and a project targeting an automated prover may want the alias kept deliberately.
- *Fidelity:* none.

### Ex 5.2.5 — `konig_matrix` (L1899, sorry)
**KEEP_CORE · high · named theorem (alternative formulation) · Core/**
- *Source:* (König) "minimum lines covering all 1s = maximum independent set of 1s in a `(0,1)`-matrix."
- *Downstream:* prose-cited by `konig_matching_covering`.
- *Existing equivalent:* the graph form exists locally (`konig_matching_covering`); the **matrix** form is a materially different interface and is not in Mathlib.
- *Reasoning:* the matrix formulation is the one applied outside graph theory (assignment problems, Latin squares); worth keeping as a distinct entry point.
- *Fidelity:* the extremal quantities are rendered as `IsLeast`/`IsGreatest` hypotheses rather than `sInf`/`sSup` values — equivalent, more usable.

### Ex 5.2.6(a) — `konig_ore_defect` (L1950, sorry)
**KEEP_CORE · high · generalisation of Theorem 5.2 · Core/**
- *Source:* (König, Ore) the defect formula for the maximum matching in a bipartite graph.
- *Downstream:* prose-cited by Ex 5.2.6(b).
- *Reasoning:* the source explicitly labels it "the following generalisation of Hall's theorem (5.2)"; it computes the maximum matching size rather than merely testing for a perfect one, so it strictly subsumes Hall.
- *Fidelity:* ⚠ stated additively to dodge ℕ-subtraction, but the **inner** `S.ncard - (⋃ …).ncard` is still ℕ-subtraction; recorded in the docstring.

### Ex 5.2.6(b) — `exists_matching_card_eq_of_card_edges_gt` (L1994, sorry)
**KEEP_CORE · medium · corollary / sharp threshold · Core/**
- *Source:* "if `|X| = |Y| = n` and `ε > (k-1)n`, then `G` has a matching of cardinality `k`."
- *Downstream:* prose-cited by Ex 5.2.6(a).
- *Constants:* `(k-1)n` is a **sharp threshold** — `k-1` full rows give exactly that many edges with no `k`-matching.
- *Reasoning:* an extremal criterion, sharp, and derivable two ways (defect formula or König).
- *Fidelity:* ⚠ the statement asks for a matching of cardinality **exactly** `k`; the argument produces one of cardinality **at least** `k`. Recorded in the docstring; see §C.

### Ex 5.2.8(a) — `doublyStochastic_card_eq` (L2039, sorry)
**KEEP_CORE · medium · reusable lemma · Core/**
- *Source:* (starred) "every doubly stochastic matrix is necessarily square."
- *Downstream:* prose-cited by `birkhoff_von_neumann`.
- *Existing equivalent:* **none** — Mathlib's `doublyStochastic` is square *by type*, making the literal book statement unstateable there. The Lean version restates it for a genuinely rectangular `Matrix m n ℝ` with unit row and column sums, which is a real theorem Mathlib does not have.
- *Constants:* the row/column sum `1` is the definition.
- *Reasoning:* a case where the restatement adds content rather than duplicating it.
- *Fidelity:* ⚠ **restated, not transcribed** — deliberately, and documented.

### Ex 5.2.8(b) — `birkhoff_von_neumann` (L2088, sorry)
**DROP_FROM_LIBRARY · high · duplicate · ExtractionArchive**
- *Source:* (Birkhoff, von Neumann) doubly stochastic = convex combination of permutation matrices.
- *Existing equivalent:* **yes** — the docstring says "**This is a one-liner.** Mathlib proves it as [`doublyStochastic_eq_sum_perms`]… the repo statement already adopts Mathlib's shape, so no translation is needed."
- *Reasoning:* a statement that has deliberately been written to match a Mathlib lemma exactly is a duplicate by construction.
- *Fidelity:* none.

### Ex 5.2.9 — `exists_common_coset_transversal` (L2141, sorry)
**KEEP_CORE · medium · named theorem (application) · Core/**
- *Source:* (P. Hall) common transversal for the left and right cosets of a subgroup.
- *Downstream:* none.
- *Existing equivalent:* not found in Mathlib.
- *Reasoning:* attributed, and the canonical group-theoretic application of Hall's theorem — a distinct reuse target from the graph statements.
- *Fidelity:* ⚠ the two conclusions are rendered as `Function.Bijective` of coset maps; the docstring flags this rendering as needing checking. See §C.

### Ex 5.3.2 — `perfectMatching_of_edgeConnected_regular` (L2191, sorry)
**KEEP_CORE · high · generalisation of Corollary 5.4 · Core/**
- *Source:* "Prove the following generalisation of corollary 5.4: a `(k-1)`-edge-connected `k`-regular graph with `ν` even has a perfect matching."
- *Downstream:* prose-cited by `IsEdgeCut`, `edgeConnectivity`.
- *Constants:* `k-1` is the exact connectivity needed; the source labels this a generalisation of the `k = 3` corollary.
- *Reasoning:* the source itself frames it as the general theorem of which a chapter corollary is the instance.
- *Fidelity:* ⚠ the docstring notes `hν : Even (Fintype.card V)` is **not used** by the intended argument — a possibly redundant hypothesis. See §C.

### Ex 5.3.3 — `isTree_perfectMatching_iff` (L2241, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* (Chungphaisan) "a tree `G` has a perfect matching iff `o(G-v) = 1` for all `v`."
- *Downstream:* none yet.
- *Upstream:* Ex 5.1.2.
- *Reasoning:* an iff-characterisation specialising Tutte's condition to trees, i.e. a decidable criterion.
- *Fidelity:* ⚠ the docstring flags that the `(⇐)` direction does not follow from `tutte_perfect_matching` alone.

### Ex 5.3.4 — `berge_tutte_defect` (L2291, sorry)
**KEEP_CORE · high · generalisation of Theorem 5.4 · Core/**
- *Source:* (starred, Berge) "the number of edges in a maximum matching is `½(ν - d)` where `d = max_S {o(G-S) - |S|}`."
- *Downstream:* none yet.
- *Constants:* `d = 0` recovers Tutte's theorem exactly — the source says so.
- *Reasoning:* the general-graph counterpart of the König–Ore defect formula; strictly subsumes Theorem 5.4.
- *Fidelity:* ⚠ same inner-ℕ-subtraction caveat as `konig_ore_defect`.

### Ex 5.3.5(b) — `perfectMatching_of_card_edges_gt` (L2342, sorry)
**KEEP_CORE · high · sharp threshold · Core/**
- *Source:* "`ν` even, `δ < ν/2`, `ε > C(δ,2) + C(ν-2δ-1,2) + δ(ν-δ)` ⇒ perfect matching."
- *Downstream:* none yet.
- *Constants:* the three-term threshold is the exact extremal count; the docstring notes "Step 4's split is where the exact form of the threshold comes from" — it is derived, not chosen.
- *Reasoning:* an extremal edge threshold for perfect matchings; the constants are the content.
- *Fidelity:* none.

---

## A.5 `EdgeColourings.lean` — chapter 6 (14 declarations)

### Ex 6.1.1 — `edgeChromaticNumber_completeBipartiteGraph` (L992, sorry)
**KEEP_EXAMPLE · medium · structural special case (subsumed) · Examples/**
- *Source:* "By finding an appropriate edge colouring, show `χ'(K_{m,n}) = Δ`."
- *Downstream:* prose-cited by `edgeChromaticNumber_completeGraph_even`.
- *Existing equivalent:* **yes, locally** — `edgeChromaticNumber_eq_maxDegree_of_isBipartite` (Theorem 6.1, König) subsumes it entirely, since `K_{m,n}` is bipartite.
- *Constants:* `m`, `n` are parameters.
- *Reasoning:* the exercise's content is an *explicit colouring* (`a + b mod Δ`), which is a construction, not new theory. It is worth keeping as a concrete instance and as the one route to the value that does not go through the currently-blocked Euler/Vizing chain, but it does not deserve a core-API slot alongside the theorem that implies it. **Flagged for human review** (§E) — if the build order argument matters more than API cleanliness, promote to `KEEP_CORE`.
- *Fidelity:* none.

### Ex 6.1.2 — `petersenGraph_edgeChromaticNumber` (L1037, sorry)
**DEFER · high · counterexample (blocked) · Deferred/**
- *Source:* "The Petersen graph is 4-edge-chromatic."
- *Downstream:* prose-cited 5×, including from `PlanarGraphs.lean`.
- *Upstream:* `petersenGraph` in **this file** (L310) is `:= sorry`; the docstring says "nothing below is provable while it is an opaque constant."
- *Constants:* `4` is the exact value and the witness that Vizing's bound `Δ+1` is attained by a cubic graph.
- *Reasoning:* a canonical class-2 witness, currently vacuous. Blocked only on the duplicate definition problem (§D.1).
- *Fidelity:* faithful once the definition is real.

### Ex 6.1.3(a) — `exists_regular_bipartite_supergraph` (L1090, sorry)
**KEEP_CORE · medium · reusable lemma · Core/**
- *Source:* "If `G` is bipartite, `G` has a `Δ`-regular bipartite supergraph."
- *Downstream:* prose-cited by `edgeChromaticNumber_eq_maxDegree_of_isBipartite` (Theorem 6.1's alternative proof) and `exists_regular_supergraph`.
- *Reasoning:* the standard regularisation/padding step; part (b) of the same exercise uses it plus Ex 5.2.3(a) to reprove König.
- *Fidelity:* ⚠ the docstring flags that `↪g` is an **induced** embedding, so no padding edge may join two vertices already non-adjacent in `G` — "would make the statement false. Worth checking carefully before proving." See §C.

### Ex 6.1.6 — `exists_edge_colouring_all_represented_of_isBipartite` (L1140, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (R. P. Gupta) "bipartite with `δ > 0` ⇒ a `δ`-edge colouring with all `δ` colours at each vertex."
- *Downstream:* none yet.
- *Constants:* `δ` is the exact number of colours — the dual of the `Δ` statement.
- *Reasoning:* an attributed theorem, and the "lower" companion to König's `Δ` theorem.
- *Fidelity:* ⚠ `Fin G.minDegree` makes the colour count a dependent type; noted.

### Ex 6.2.1 — `edgeChromaticNumber_completeGraph_odd` (L1190, sorry)
**KEEP_CORE · high · reusable computation / sharp value · Core/**
- *Source:* (starred) "`χ'(K_{2n-1}) = χ'(K_{2n}) = 2n - 1`."
- *Downstream:* prose-cited by the even case and by `edgeChromaticNumber_eq_maxDegree_add_one_of_regular_odd_card`.
- *Constants:* `2n-1` odd order is a **named structural class** (odd complete graphs are the canonical class-2 family); the value `2n-1` is exact.
- *Reasoning:* the odd case is the interesting half — `Δ = 2n-2` but `χ' = 2n-1`, so it witnesses class 2.
- *Fidelity:* ⚠ `2*n - 1` truncates at `n = 0`, which `hn : 0 < n` rules out.

### Ex 6.2.1 — `edgeChromaticNumber_completeGraph_even` (L1231, sorry)
**KEEP_CORE · high · reusable computation · Core/**
- *Source:* same exercise, even half.
- *Downstream:* prose-cited 2×.
- *Constants:* `2n` even order; the value `2n-1 = Δ` shows class 1.
- *Reasoning:* the even/odd pair together is the standard class-1/class-2 dichotomy example; both halves are separately cited.
- *Fidelity:* ⚠ its proof route crosses into `Matchings.lean`, which this file does not import.

### Ex 6.2.2 — `edgeChromaticNumber_eq_maxDegree_add_one_of_regular_odd_card` (L1270, sorry)
**KEEP_CORE · high · reusable criterion · Core/**
- *Source:* "a nonempty regular simple graph with `ν` odd has `χ' = Δ + 1`."
- *Downstream:* none yet.
- *Constants:* regularity + odd order is the classical class-2 criterion; both are essential (the parity is what blocks a perfect matching).
- *Reasoning:* a general criterion, of which Ex 6.2.1's odd case is the instance.
- *Fidelity:* none.

### Ex 6.2.3(a) — `edgeChromaticNumber_eq_maxDegree_add_one_of_card_edges_gt` (L1311, sorry)
**KEEP_CORE · high · reusable criterion / sharp threshold · Core/**
- *Source:* (Vizing) "`ν = 2n + 1` and `ε > nΔ` ⇒ `χ' = Δ + 1`."
- *Downstream:* prose-cited 4× — the docstring itself annotates it "Reusable."
- *Constants:* `nΔ` is the maximum number of edges a proper `Δ`-colouring of an odd-order graph can carry — a **sharp counting threshold**, not an example value.
- *Reasoning:* the file's own most-reused class-2 criterion; three later exercises are deduced from it.
- *Fidelity:* none.

### Ex 6.2.3(b)(i) — `edgeChromaticNumber_subdivide_eq_maxDegree_add_one` (L1359, sorry)
**KEEP_CORE · high · named corollary · Core/**
- *Source:* (Beineke, Wilson) subdividing one edge of an even-order regular graph forces `χ' = Δ + 1`.
- *Downstream:* prose-cited 4×.
- *Constants:* `2 ≤ k` is **load-bearing** — at `k = 1` the new degree-2 vertex changes `Δ` and the conclusion fails.
- *Reasoning:* attributed, and a genuine class-2 construction principle.
- *Fidelity:* ⚠ needs degree/edge-count lemmas for `subdivide` that this file lacks.

### Ex 6.2.3(b)(ii) — `edgeChromaticNumber_deleteEdges_eq_maxDegree_add_one` (L1402, sorry)
**KEEP_CORE · high · named corollary · Core/**
- *Source:* (Beineke, Wilson) deleting fewer than `k/2` edges from an odd-order `k`-regular graph keeps `χ' = Δ + 1`.
- *Downstream:* prose-cited 4×.
- *Constants:* `2 * F.card < k` (i.e. `|F| < k/2`) is the **exact** threshold — enough edges must remain that some vertex keeps full degree.
- *Reasoning:* attributed, sharp, and a companion to (b)(i).
- *Fidelity:* none.

### Ex 6.2.4(a) — `exists_regular_supergraph` (L1448, sorry)
**DEFER · medium · likely unstateable as written · Deferred/**
- *Source:* "If `G` is loopless, `G` has a `Δ`-regular loopless supergraph."
- *Downstream:* none.
- *Reasoning:* the docstring records two obstructions: the book's construction "needs **multi-edges**", which `SimpleGraph` cannot express, and the `↪g` is an *induced* embedding so no padding edge is permitted between existing vertices. Both point at the statement being unprovable in this encoding rather than merely unproved.
- *Fidelity:* ⚠ likely false / unrepresentable in `SimpleGraph`. See §C.

### Ex 6.2.5 — `isHamiltonian_of_uniquely_three_edge_colourable` (L1503, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (Greenwell, Kronk) "every uniquely 3-edge-colourable 3-regular graph is hamiltonian."
- *Downstream:* prose-cited by `IsUniquelyEdgeColourable`.
- *Constants:* `3` in both places is a **named structural class** (cubic, 3-edge-colourable); the statement is specific to it.
- *Reasoning:* attributed and a genuine structural theorem.
- *Fidelity:* ⚠ `hcol : G.lineGraph.Colorable 3` is **mandatory** — without it uniqueness is vacuous and the Petersen graph is a counterexample. The hypothesis is present and correctly flagged.

### Ex 6.2.6(a) — `edgeChromaticNumber_boxProd_completeGraph_two` (L1557, sorry)
**KEEP_CORE · high · base case · Core/**
- *Source:* "Using Vizing, `χ'(G × K₂) = Δ(G × K₂)`."
- *Downstream:* prose-cited by part (b).
- *Constants:* `K₂` is the base of the product induction; the `2` is structural.
- *Reasoning:* the base case that (b) is deduced from — a real dependency.
- *Fidelity:* the book's "product" is Mathlib's `boxProd` (`□`); identified correctly.

### Ex 6.2.6(b) — `edgeChromaticNumber_boxProd` (L1608, sorry)
**KEEP_CORE · high · reusable theorem · Core/**
- *Source:* "if `H` is nontrivial with `χ'(H) = Δ(H)`, then `χ'(G × H) = Δ(G × H)`."
- *Downstream:* prose-cited by part (a).
- *Reasoning:* a class-1 preservation theorem for products — reusable for any product construction.
- *Fidelity:* none.

---

## A.6 `IndependentSetsCliques.lean` — chapter 7 (27 declarations)

### Ex 7.2.1 — `ramseyNumber_comm` (L1845, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "`r(k, l) = r(l, k)`."
- *Downstream:* prose-cited by `ramseyNumber_one_right`.
- *Reasoning:* a symmetry lemma is the cheapest and most frequently applied normalisation step in any Ramsey argument.
- *Fidelity:* none.

### Ex 7.2.4(a) — `indepNum_composition_le` (L2044, sorry)
**KEEP_CORE · high · reusable bound · Core/**
- *Source:* "`α(G[H]) ≤ α(G)α(H)`."
- *Downstream:* prose-cited 4× (`ramsey_product_lower`, `abbott_lower_bound`, `ramseyNumber_ge_of_min`, `composition`).
- *Reasoning:* the multiplicative bound underlying every product construction for Ramsey lower bounds.
- *Fidelity:* none.

### Ex 7.2.4(b) — `ramsey_product_lower` (L2088, sorry)
**KEEP_CORE · high · reusable bound · Core/**
- *Source:* the product lower bound `r(kl+1,kl+1) - 1 ≥ (r(k+1,k+1)-1)(r(l+1,l+1)-1)`.
- *Downstream:* prose-cited 4×, notably by `abbott_lower_bound`.
- *Constants:* the `+1`s are the clique-size offsets; the multiplicative shape is the content.
- *Reasoning:* the engine of iterated Ramsey lower bounds.
- *Fidelity:* ⚠ requires `(G[H])ᶜ ≅ Gᶜ[Hᶜ]`, "**true but not obvious** and is not stated in this file" — a missing supporting lemma. See §C.

### Ex 7.2.4(c) — `abbott_lower_bound` (L2128, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (H. L. Abbott) "`r(2ⁿ+1, 2ⁿ+1) ≥ 5ⁿ + 1`."
- *Downstream:* prose-cited 4×.
- *Constants:* `5` is `r(3,3) - 1` — it is **derived from the base case**, not chosen. `2ⁿ` is the iteration of the product bound.
- *Reasoning:* an attributed lower bound whose constants encode the recursion; exactly the case where a fixed number is mathematical content.
- *Fidelity:* ⚠ needs `r(3,3) = 6`; only `6 ≤ r(3,3)` is available locally. Blocked but stateable.

### Ex 7.2.5 — `grahamGraph_cliqueFree_six` (L2181, sorry)
**KEEP_EXAMPLE · high · witness (half) · Examples/**
- *Source:* "the join of a 3-cycle and a 5-cycle contains no `K₆`."
- *Downstream:* prose-cited by `grahamGraph`, `grahamGraph_monochromatic_triangle`.
- *Upstream:* `grahamGraph` is **honest** — not vacuous.
- *Constants:* `3`, `5`, `6` are the specific Graham construction; they are the witness's data.
- *Reasoning:* half of a two-part witness (see below); a property of one named graph.
- *Fidelity:* none.

### Ex 7.2.5 — `grahamGraph_monochromatic_triangle` (L2227, sorry)
**KEEP_EXAMPLE · high · witness (half) · Examples/**
- *Source:* "…but every 2-edge colouring yields a monochromatic triangle."
- *Downstream:* prose-cited by `grahamGraph`, `grahamGraph_cliqueFree_six`.
- *Reasoning:* together with the previous entry this is Graham's minimal Folkman-type witness — a `K₆`-free graph that is Ramsey for triangles. A concrete construction, not an inference step.
- *Fidelity:* ⚠ `χ` is a total function on **all** of `Sym2 (Fin 3 ⊕ Fin 5)`, not only on edges — a slightly stronger hypothesis than the book's. Recorded.

### Ex 7.2.6(a) — `generalisedRamsey_path_path` (L2293, sorry)
**KEEP_EXAMPLE · high · computation / benchmark · Examples/**
- *Source:* "`r(P₄, P₄) = 5`."
- *Downstream:* prose-cited 6× within the generalised-Ramsey family.
- *Constants:* `5` is the exact value for this specific pair — a table entry.
- *Reasoning:* small exact Ramsey values are reference data and excellent regression tests for `generalisedRamseyNumber`, but a prover cannot reuse `r(P₄,P₄) = 5` on any other goal.
- *Fidelity:* ⚠ "path of length three" means **three edges**, hence `pathGraph 4`, not `pathGraph 3`. The transcription is correct; the docstring flags it as easy to get wrong.

### Ex 7.2.6(a) — `generalisedRamsey_path_cycle` (L2322, sorry)
**KEEP_EXAMPLE · high · computation / benchmark · Examples/** — same exercise, `r(P₄, C₄) = 5`. Constants: exact table value. Downstream: prose-cited 6×. Fidelity: none.

### Ex 7.2.6(a) — `generalisedRamsey_cycle_cycle` (L2351, sorry)
**KEEP_EXAMPLE · high · computation / benchmark · Examples/** — same exercise, `r(C₄, C₄) = 6`. Constants: exact table value. Downstream: prose-cited 6×. Fidelity: none.

### Ex 7.2.6(b) — `generalisedRamsey_tree_star` (L2441, sorry)
**KEEP_CORE · high · named general theorem · Core/**
- *Source:* (starred, Chvátal) "if `T` is a tree on `m` vertices and `(m-1) ∣ (n-1)`, then `r(T, K_{1,n}) = m + n - 1`."
- *Downstream:* prose-cited 6×.
- *Constants:* `m`, `n` are parameters; the divisibility condition is essential to the exact value.
- *Reasoning:* a general theorem over all trees, attributed — a real reuse target, unlike the fixed values of part (a).
- *Fidelity:* ⚠ the two targets live on different carriers (`W` and `Fin 1 ⊕ Fin n`), forcing a heterogeneous spelling of `generalisedRamseyNumber`.

### Ex 7.2.6(c) — `chvatal_tree_complete` (L2489, sorry)
**KEEP_CORE · high · named general theorem · Core/**
- *Source:* (starred, Chvátal) "`r(T, Kₙ) = (m-1)(n-1) + 1` for any tree `T` on `m` vertices."
- *Downstream:* prose-cited 6×.
- *Constants:* the formula is exact and general.
- *Reasoning:* Chvátal's tree–complete Ramsey theorem; one of the few generalised Ramsey numbers known in closed form.
- *Fidelity:* ⚠ same heterogeneous-carrier spelling as (b); the upper bound needs §7.3's Turán-type theorem.

### Ex 7.3.1 — `nine_people_triangle` (L2777, sorry)
**KEEP_EXAMPLE · high · computation / puzzle · Examples/**
- *Source:* "In a group of nine people with degree sequence `(2,4,4,5,5,5,5,6,6)`, three all know one another."
- *Downstream:* none.
- *Constants:* `9` and the degree multiset are **arbitrary example values** chosen to sit just above the Turán threshold — they carry no structural meaning beyond this instance.
- *Reasoning:* a worked application of Turán's bound to one degree sequence. Useful as a decision-procedure regression test (`#(turanGraph 9 2).edgeFinset = 20`), no reuse.
- *Fidelity:* none.

### Ex 7.3.3(a) — `triangle_of_card_edgeFinset_gt` (L2816, sorry)
**KEEP_CORE · high · sharp threshold (Mantel) · Core/**
- *Source:* "if `G` is simple and `ε > ν²/4`, then `G` contains a triangle."
- *Downstream:* prose-cited by 7.3.3(b) and 7.3.3(c).
- *Existing equivalent:* derivable from the local `turan_edge_bound`; Mathlib has Turán's theorem. But the Mantel form (`ε > ν²/4 ⇒ K₃`) is the standard retrieval shape and is not a Mathlib alias.
- *Constants:* `ν²/4` is **sharp**, attained by the balanced complete bipartite graph — which part (b) exhibits.
- *Reasoning:* the canonical sharp extremal threshold of the chapter.
- *Fidelity:* stated as `ν² < 4ε` to avoid ℕ-division.

### Ex 7.3.3(b) — `completeBipartite_triangle_free_extremal` (L2857, sorry)
**KEEP_EXAMPLE · high · sharpness witness · Examples/**
- *Source:* "Find a simple `G` with `ε = ⌊ν²/4⌋` containing no triangle."
- *Downstream:* prose-cited by 7.3.3(a) and (c).
- *Constants:* `⌊ν/2⌋`, `ν - ⌊ν/2⌋` are the balanced split — the extremal configuration.
- *Reasoning:* it certifies that (a)'s threshold cannot be lowered. Retention is essential; but its role is witness, not inference step.
- *Fidelity:* ⚠ needs `ε(K_{m,n}) = mn` from `GraphsAndSubgraphs.lean`, which this file does not import.

### Ex 7.3.3(c) — `triangle_of_not_bipartite_of_card_edgeFinset_gt` (L2903, sorry)
**KEEP_CORE · high · sharp threshold · Core/**
- *Source:* (starred, Erdős) "simple, not bipartite, `ε > ((ν-1)²/4) + 1` ⇒ triangle."
- *Downstream:* prose-cited by (a) and (b).
- *Constants:* `((ν-1)²/4) + 1` is a strictly better threshold than (a)'s under the extra non-bipartite hypothesis — sharp for the odd-cycle-plus-bipartite extremal graph.
- *Reasoning:* the docstring is explicit: "⚠ **Not a corollary of Turán**". Independent content, attributed, sharp.
- *Fidelity:* none.

### Ex 7.3.4(a) — `isContained_completeBipartite_two_of_sum_choose_gt` (L2976, sorry)
**KEEP_CORE · high · reusable bound (Kővári–Sós–Turán) · Core/**
- *Source:* (starred) "`∑_v C(d(v),2) > (m-1)C(ν,2)` ⇒ `G ⊇ K_{2,m}` (`m ≥ 2`)."
- *Downstream:* prose-cited 4× (7.3.4(b), 7.3.4(c), 7.3.5, `unitDistanceGraph`).
- *Constants:* `2` in `K_{2,m}` is the case being counted (cherries); `m` is a parameter.
- *Reasoning:* the double-counting core of the Zarankiewicz/KST family, and the direct engine of the unit-distance bound.
- *Fidelity:* none.

### Ex 7.3.4(b) — `isContained_completeBipartite_two_of_card_edgeFinset_gt` (L3020, sorry)
**KEEP_CORE · high · corollary bound · Core/**
- *Source:* the real-valued edge-count form of (a).
- *Downstream:* prose-cited 4×.
- *Constants:* the exponents `1/2` and `3/2` are the KST exponents for `K_{2,m}` — they are the mathematical content.
- *Reasoning:* the usable form (an edge count, not a degree sum), and what (c) applies.
- *Fidelity:* ⚠ irreducibly real-valued (`rpow`); the proof leaves ℕ early.

### Ex 7.3.4(c) — `card_unit_distance_pairs_le` (L3093, sorry)
**KEEP_CORE · high · named application / sharp-order bound · Core/**
- *Source:* "given `n` points in the plane, at most `n^{3/2}/√2 + n/4` pairs are at distance exactly 1."
- *Downstream:* prose-cited 4×.
- *Constants:* `3/2`, `√2`, `4` come from applying (b) with `m = 2`; the exponent `3/2` is the classical Erdős unit-distance bound.
- *Reasoning:* the headline geometric application of the chapter; a genuine theorem, not an instance.
- *Fidelity:* ⚠ the geometric step ("two distinct points have at most two common unit-distance neighbours") is **not in Mathlib** and must be built.

### Ex 7.3.5 — `isContained_completeBipartite_of_card_edgeFinset_gt` (L3138, sorry)
**KEEP_CORE · high · general Kővári–Sós–Turán · Core/**
- *Source:* "`ε > ((m-1)^{1/m} ν^{2-1/m})/2 + ((m-1)ν)/2 ⇒ G ⊇ K_{m,m}`."
- *Downstream:* prose-cited by 7.3.4(a).
- *Constants:* the exponent `2 - 1/m` varies with `m` — this is the general KST bound, of which 7.3.4(b) is the `m = 2` case.
- *Reasoning:* the general theorem; it subsumes 7.3.4(a)/(b) but is stated separately in the source and both are worth keeping (7.3.4 is the sharper `m = 2` form).
- *Fidelity:* ⚠ real-valued with `rpow`; noted.

### Ex 7.4.1 — `schurNumber_one` (L3260, sorry)
**KEEP_EXAMPLE · high · computation · Examples/**
- *Source:* "`s₁ = 2`."
- *Downstream:* prose-cited within the Schur family.
- *Constants:* an exact table value.
- *Reasoning:* a single numeric fact with no downstream consumer; a decidability benchmark.
- *Fidelity:* none.

### Ex 7.4.1 — `schurNumber_two` (L3286, sorry)
**KEEP_EXAMPLE · high · computation · Examples/** — `s₂ = 5`. Same reasoning; no downstream consumer.

### Ex 7.4.1 — `schurNumber_three` (L3316, sorry)
**KEEP_CORE · high · base case · Core/**
- *Source:* "`s₃ = 14`."
- *Downstream:* **explicitly required by Ex 7.4.2(b)** — the source says "Using (a) and the fact that `s₃ = 14`…".
- *Constants:* `14` is the **base case of the lower-bound recursion**, which is exactly why `27 · 3^{n-3}` appears in 7.4.2(b) (`27 = 2·14 - 1`).
- *Reasoning:* unlike `s₁` and `s₂`, this value is a load-bearing input to a general theorem. A fixed number that is a base case, not an example value.
- *Fidelity:* none.

### Ex 7.4.2(a) — `schurNumber_recursion` (L3352, sorry)
**KEEP_CORE · high · reusable recursion · Core/**
- *Source:* "`sₙ ≥ 3s_{n-1} - 1`."
- *Downstream:* prose-cited by 7.4.2(b).
- *Constants:* `3` and `-1` are the recursion's coefficients, derived from the tripling construction.
- *Reasoning:* the inference step that generates every Schur lower bound.
- *Fidelity:* stated as `3 * s(n-1) ≤ s(n) + 1` to avoid ℕ-subtraction. ⚠ the docstring notes the `sInf` set must be upward closed for this reading to be correct.

### Ex 7.4.2(b) — `schurNumber_lower_bound` (L3387, sorry)
**KEEP_CORE · high · corollary (headline bound) · Core/**
- *Source:* "`sₙ ≥ ½(27·3^{n-3} + 1)`."
- *Downstream:* prose-cited by (a).
- *Constants:* `27 = 2·14 - 1` and the exponent shift `n-3` both come from the base case `s₃ = 14` — derived, not chosen.
- *Reasoning:* the closed-form lower bound the chapter is aiming at.
- *Fidelity:* stated as `27·3^{n-3} + 1 ≤ 2·sₙ` to avoid halving.

### Ex 7.5.1(a) — `card_unitDistanceGraph_le_of_diam_one` (L3583, sorry)
**KEEP_CORE · high · sharp bound · Core/**
- *Source:* (starred) "in a planar set of diameter 1, at most `n` pairs are at distance 1."
- *Downstream:* prose-cited by 7.5.1(b).
- *Constants:* the bound `n` is **exactly attained** — part (b) constructs a set achieving it.
- *Reasoning:* a sharp geometric extremal bound.
- *Fidelity:* ⚠ the key step (the diameter-1 constraint forces the unit-distance graph to be sparse) is "not a standard graph [lemma]" and not in Mathlib.

### Ex 7.5.1(b) — `exists_unitDistanceGraph_card_eq` (L3628, sorry)
**KEEP_EXAMPLE · high · sharpness witness · Examples/**
- *Source:* (E. Pannwitz) construct a diameter-1 set with exactly `n` unit-distance pairs.
- *Downstream:* prose-cited by (a).
- *Reasoning:* certifies (a) is sharp; a Reuleaux-polygon construction, not an inference step.
- *Fidelity:* ⚠ the Reuleaux construction is natural for **odd** `n`, but the signature asks for all `n ≥ 3`. See §C.

### Ex 7.5.2 — `police_cars` (L3697, sorry)
**KEEP_EXAMPLE · medium · application / puzzle · Examples/**
- *Source:* "18 police cars in a radius-6 city with radio range 9: two cars each reach at least five others."
- *Downstream:* prose-cited by `radioGraph`.
- *Constants:* `18`, `6`, `9`, `5` are **arbitrary example values** of a Ramsey/pigeonhole application.
- *Reasoning:* a worked application; no reuse.
- *Fidelity:* ⚠ the docstring flags that the natural partition into six sectors gives diameter `6√3 ≈ 10.39 > 9`, so the naive proof plan **does not work**. The statement may still be true, but the recorded route is broken. See §E.

---

## A.7 `VertexColourings.lean` — chapter 8 (38 declarations)

### Ex 8.1.1 — `chromaticNumber_ge_of_card_edges` (L926, sorry)
**KEEP_CORE · high · reusable bound · Core/**
- *Source:* "if `G` is simple, `χ ≥ ν²/(ν² - 2ε)`."
- *Downstream:* none yet.
- *Constants:* the shape `ν²/(ν² - 2ε)` is the Cauchy–Schwarz bound on colour-class sizes; sharp for complete multipartite graphs.
- *Reasoning:* a general lower bound on `χ` from the edge count — one of very few, and directly usable.
- *Fidelity:* stated multiplicatively over `ℝ`.

### Ex 8.1.2 — `chromaticNumber_le_five_of_odd_cycles_meet` (L962, sorry)
**KEEP_CORE · high · structural theorem · Core/**
- *Source:* "if any two odd cycles of `G` share a vertex, `χ ≤ 5`."
- *Downstream:* none yet.
- *Constants:* `5` is **essential to the truth** — it is the exact bound this hypothesis yields (`K₅` shows it cannot be `4`).
- *Reasoning:* the skeleton also notes that its step 0 — `χ(G) ≤ χ(G[A]) + χ(G[Aᶜ])` — is a "reusable splitting lemma"; that lemma should be extracted, but the theorem itself is core.
- *Fidelity:* none.

### Ex 8.1.3 — `welsh_powell` (L1010, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (Welsh, Powell) "`χ ≤ maxᵢ min{dᵢ + 1, i}`."
- *Downstream:* prose-cited by 8.1.4(a) and 8.1.4(b), both of which are deduced from it.
- *Reasoning:* the greedy-colouring bound; two later exercises are explicitly "using exercise 8.1.3".
- *Fidelity:* the sorted degree sequence is rendered via `σ : Fin ν ≃ V` with `Antitone`; faithful.

### Ex 8.1.4(a) — `chromaticNumber_le_ceil_sqrt_two_mul_card_edges` (L1052, sorry)
**KEEP_CORE · high · reusable bound · Core/**
- *Source:* "`χ ≤ ⌈√(2ε)⌉`."
- *Downstream:* prose-cited by `nordhaus_gaddum`, `welsh_powell`.
- *Constants:* `√(2ε)` is the standard edge-count colouring bound.
- *Reasoning:* a general bound with a clean statement.
- *Fidelity:* ⚠ **statement deliberately repaired.** The book's version is **false** for the edgeless graph on a nonempty carrier (`χ = 1`, `⌈√0⌉ = 0`); the Lean version adds `1 ≤ ε`. Documented, and the right repair. See §C.

### Ex 8.1.4(b) — `nordhaus_gaddum` (L1090, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (Nordhaus, Gaddum) "`χ(G) + χ(Gᶜ) ≤ ν + 1`."
- *Downstream:* prose-cited by 8.1.3, 8.1.4(a).
- *Constants:* `ν + 1` is **sharp** (equality for complete graphs and their complements).
- *Reasoning:* attributed, sharp, and one of the best-known complement inequalities.
- *Fidelity:* none.

### Ex 8.1.5 — `szekeres_wilf` (L1130, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (Szekeres, Wilf) "`χ(G) ≤ 1 + max δ(H)` over induced subgraphs `H`."
- *Downstream:* none yet.
- *Constants:* the `1 +` is the degeneracy offset, exact.
- *Reasoning:* the degeneracy bound — strictly stronger than `χ ≤ Δ + 1` and the standard tool for sparse graphs.
- *Fidelity:* ⚠ the `sup` includes `s = ∅`, whose `minDegree` is `0` by Mathlib's convention; harmless but noted.

### Ex 8.1.6 — `gallai_two_per_class` (L1180, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (starred, T. Gallai) if a `k`-chromatic graph has *some* colouring with every colour used twice, it has a `k`-colouring of that type.
- *Downstream:* none yet.
- *Constants:* `2` per class is the property being preserved.
- *Reasoning:* attributed, starred as difficult, and a genuine structural statement about the space of optimal colourings.
- *Fidelity:* none.

### Ex 8.1.7 — `isKCritical_one_iff` (L1258, sorry)
**KEEP_CORE · high · structural characterisation (base case) · Core/**
- *Source:* "the only 1-critical graph is `K₁`."
- *Downstream:* prose-cited 8× within the criticality family.
- *Constants:* `1` indexes the base case of the critical-graph classification.
- *Reasoning:* base case of a three-part classification; needed by the `mycielskiTower` induction and by Brooks.
- *Fidelity:* none.

### Ex 8.1.7 — `isKCritical_two_iff` (L1287, sorry)
**KEEP_CORE · high · structural characterisation (base case) · Core/**
- *Source:* "the only 2-critical graph is `K₂`."
- *Downstream:* prose-cited 8×; explicitly the base case of `mycielskiTower_isKCritical` (`G₂ = K₂`).
- *Reasoning:* as above; a load-bearing base case, not a numeric curiosity.
- *Fidelity:* none.

### Ex 8.1.7 — `isKCritical_three_iff_odd_cycle` (L1224, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "the only 3-critical graphs are the odd cycles `C_k`, `k ≥ 3`."
- *Downstream:* prose-cited 8×, including `brooks_chromaticNumber_le_maxDegree` and `brooks_iff_edge_bound` — Brooks' theorem's odd-cycle exception is exactly this classification.
- *Constants:* `3` is the first nontrivial case; the odd-cycle family is the complete answer.
- *Reasoning:* the substantive third of the classification and a direct dependency of Brooks.
- *Fidelity:* none.

### Ex 8.1.8 — `IsKCritical.not_uniquelyColorable_of_isVertexCut` (L1328, sorry)
**KEEP_CORE · high · structural theorem · Core/**
- *Source:* "no vertex cut of a `k`-critical graph induces a uniquely `(k-1)`-colourable subgraph."
- *Downstream:* prose-cited by `IsCritical.not_isClique_of_isVertexCut`, `UniquelyColorable`.
- *Reasoning:* a criticality/connectivity structural constraint; the docstring notes it shares four of six proof steps with Theorem 8.2, i.e. it is part of the same reusable machinery.
- *Fidelity:* none.

### Ex 8.1.9(a) — `IsCritical.neighborSet_not_subset` (L1359, sorry)
**KEEP_CORE · high · reusable structural lemma · Core/**
- *Source:* "if `u`, `v` are vertices of a critical graph, `N(u) ⊄ N(v)`."
- *Downstream:* prose-cited by 8.1.9(b) and `exists_isKCritical_four`.
- *Reasoning:* a clean local constraint on critical graphs, applied wherever criticality is exploited.
- *Fidelity:* none.

### Ex 8.1.9(b) — `no_isKCritical_card_eq_succ` (L1397, sorry)
**KEEP_CORE · high · boundary case · Core/**
- *Source:* "no `k`-critical graph has exactly `k + 1` vertices."
- *Downstream:* prose-cited by 8.1.9(a), `exists_isKCritical_four`.
- *Constants:* `k + 1` is exactly the excluded order — and this is precisely what makes Ex 8.1.12's `n = 5` gap sharp.
- *Reasoning:* a boundary/impossibility result the retention policy explicitly protects.
- *Fidelity:* none.

### Ex 8.1.10(a) — `chromaticNumber_join` (L1430, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "`χ(G₁ ∨ G₂) = χ(G₁) + χ(G₂)`."
- *Downstream:* prose-cited 5× (`join_isCritical_iff`, `exists_isKCritical_four`, `numColorings_join_singleton`, `wheel`, `join`).
- *Reasoning:* the additivity of `χ` over joins is the single most reused colouring identity in the chapter — wheels, critical constructions and chromatic polynomials all go through it.
- *Fidelity:* none.

### Ex 8.1.10(b) — `join_isCritical_iff` (L1472, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "`G₁ ∨ G₂` is critical iff both are."
- *Downstream:* prose-cited 5×.
- *Reasoning:* the criticality analogue of (a); used to build critical graphs of prescribed order.
- *Fidelity:* none.

### Ex 8.1.11 — `hajos_construction` (L1525, sorry)
**KEEP_CORE · high · named construction · Core/**
- *Source:* (G. Hajós) the Hajós join of two `k`-critical graphs is `k`-critical.
- *Downstream:* prose-cited by `exists_isKCritical_four`.
- *Reasoning:* the standard generator of critical graphs; attributed and reusable as a construction principle.
- *Fidelity:* rendered on a shared carrier `V` with `G₁.support ∩ G₂.support = {v}`; a reasonable encoding of "exactly one vertex in common".

### Ex 8.1.12 — `exists_isKCritical_four` (L1565, sorry)
**KEEP_CORE · medium · sharp existence threshold · Core/**
- *Source:* "For `n = 4` and all `n ≥ 6`, construct a 4-critical graph on `n` vertices."
- *Downstream:* prose-cited by 8.1.9(b), 8.1.10(b).
- *Constants:* the case split `n = 4 ∨ n ≥ 6` is **exactly sharp**: `n = 5` is impossible by Ex 8.1.9(b) (`k + 1 = 5`). The gap at `5` is mathematical content, not a convenience.
- *Reasoning:* although its content is a construction, the *statement* records a sharp existence spectrum, which is a boundary result rather than a single witness. Classified `KEEP_CORE` for that reason; **flagged for human review** (§E) if the project prefers constructions to live in `Examples/` uniformly.
- *Fidelity:* none.

### Ex 8.1.13(a) — `kainen` (L1603, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (P. C. Kainen) "if `G[X]` and `G[Y]` are `n`-colourable and `|[X,Y]| ≤ n - 1`, then `G` is `n`-colourable."
- *Downstream:* prose-cited by 8.1.13(b), `IsEdgeCut`, `edgeConnectivity`.
- *Constants:* `n - 1` is **sharp** — with `n` crossing edges the conclusion fails.
- *Reasoning:* attributed, sharp, and the engine of Dirac's edge-connectivity result in part (b).
- *Fidelity:* none.

### Ex 8.1.13(b) — `IsKCritical.edgeConnectivity_ge` (L1643, sorry)
**KEEP_CORE · high · named corollary · Core/**
- *Source:* (G. A. Dirac) "every `k`-critical graph is `(k-1)`-edge-connected."
- *Downstream:* prose-cited by (a), `IsEdgeCut`, `edgeConnectivity`.
- *Constants:* `k - 1` is sharp.
- *Reasoning:* attributed; the standard connectivity consequence of criticality.
- *Fidelity:* none.

### Ex 8.2.1 — `brooks_iff_edge_bound` (L1771, sorry)
**KEEP_CORE · high · equivalence / reformulation · Core/**
- *Source:* "Brooks' theorem is equivalent to: if `G` is `k`-critical (`k ≥ 4`) and not complete, `2ε ≥ ν(k-1) + 1`."
- *Downstream:* none yet.
- *Constants:* `k ≥ 4` excludes the odd-cycle case (`k = 3`) — essential; `ν(k-1)+1` is the sharp edge bound.
- *Reasoning:* an equivalence between two theorem statements is exactly the kind of conceptual characterisation the policy protects; it also gives a second, counting-based route to Brooks.
- *Fidelity:* rendered as an `↔` between two universally quantified statements over all carriers — a faithful but heavy encoding.

### Ex 8.2.2 — `chromaticIndex_le_four_of_maxDegree_three` (L1817, sorry)
**KEEP_CORE · high · structural special case · Core/**
- *Source:* "Use Brooks' theorem to show that a loopless `G` with `Δ = 3` has `χ' ≤ 4`."
- *Downstream:* none yet.
- *Constants:* `3` is the **cubic class**; `4 = Δ + 1` is Vizing's bound reached via Brooks on the line graph.
- *Reasoning:* a named-class result and a distinct proof route (through Brooks, not Vizing) to a bound `EdgeColourings.lean` otherwise gets only from the blocked Vizing chain.
- *Fidelity:* the hypothesis is `maxDegree = 3` (exactly), matching the book.

### Ex 8.3.1 — `hasK4Subdivision_of_few_low_degree` (L2077, sorry)
**KEEP_CORE · high · structural theorem · Core/**
- *Source:* (starred) "if at most one vertex has degree `< 3`, `G` contains a `K₄`-subdivision."
- *Downstream:* prose-cited by 8.3.2(a).
- *Constants:* `3` is the degree threshold and `1` the allowed number of exceptions — both exact.
- *Reasoning:* a topological-minor existence theorem, reusable wherever `K₄`-subdivisions are needed (planarity, Hadwiger-type arguments).
- *Fidelity:* ⚠ **statement repaired** — the book's version is false for `card V ≤ 1`; `4 ≤ ν` was added. Documented. See §C.

### Ex 8.3.2(a) — `hasK4Subdivision_of_card_edges` (L2111, sorry)
**KEEP_CORE · high · sharp threshold · Core/**
- *Source:* (starred) "`ν ≥ 4` and `ε ≥ 2ν - 2` ⇒ `K₄`-subdivision."
- *Downstream:* prose-cited by 8.3.1, 8.3.2(b).
- *Constants:* `2ν - 2` is **sharp** — part (b) constructs a graph with `ε = 2ν - 3` and no `K₄`-subdivision.
- *Reasoning:* an extremal edge threshold with a matching witness.
- *Fidelity:* none.

### Ex 8.3.2(b) — `exists_no_hasK4Subdivision_card_edges` (L2149, sorry)
**KEEP_EXAMPLE · high · sharpness witness · Examples/**
- *Source:* "For `ν ≥ 4`, find a simple `G` with `ε = 2ν - 3` and no `K₄`-subdivision."
- *Downstream:* prose-cited by 8.3.2(a), 8.3.1.
- *Constants:* `2ν - 3` is one below (a)'s threshold — the witness value.
- *Reasoning:* certifies (a) is sharp; the fan `K₁ ∨ P_{n-1}` is one specific family.
- *Fidelity:* none.

### Ex 8.4.2(a) — `chromaticPolynomial_coeff_card_sub_one` (L2304, sorry)
**KEEP_CORE · high · reusable structural fact · Core/**
- *Source:* "the coefficient of `k^{ν-1}` in `π_k(G)` is `-ε`."
- *Downstream:* prose-cited by 8.4.2(b), `chromaticPolynomial_no_root_gt_card`, `exists_chromaticPolynomial`.
- *Constants:* `ν - 1` is the second-highest degree; `-ε` is exact.
- *Reasoning:* it lets any argument read the edge count off the polynomial — the standard way to rule out candidate chromatic polynomials.
- *Fidelity:* the polynomial is characterised by `hp : ∀ k, p.eval k = π_k(G)` rather than defined; workable.

### Ex 8.4.2(b) — `no_graph_chromaticPolynomial_eq` (L2344, sorry)
**KEEP_EXAMPLE · high · counterexample / regression test · Examples/**
- *Source:* "Deduce that no graph has chromatic polynomial `k⁴ - 3k³ + 3k²`."
- *Downstream:* prose-cited 3×.
- *Constants:* the polynomial is a **specific instance** chosen to violate (a) (`ν = 4`, `ε = 3`, but `3` edges on `4` vertices force a different `k²` coefficient).
- *Reasoning:* a single negative instance; excellent as a regression test for the coefficient machinery, no reuse as an inference step.
- *Fidelity:* none.

### Ex 8.4.3(a) — `numColorings_of_isTree` (L2379, sorry)
**KEEP_CORE · high · reusable computation · Core/**
- *Source:* "if `G` is a tree, `π_k(G) = k(k-1)^{ν-1}`."
- *Downstream:* prose-cited by 8.4.3(b), 8.4.4, `numColorings_le_of_connected`.
- *Constants:* the formula is exact and characterises trees among connected graphs (part (b)).
- *Reasoning:* the base computation of the whole chromatic-polynomial section.
- *Fidelity:* none.

### Ex 8.4.3(b) — `numColorings_le_of_connected` (L2428, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "if `G` is connected, `π_k(G) ≤ k(k-1)^{ν-1}`, with equality only for trees."
- *Downstream:* prose-cited 3×.
- *Constants:* the added `3 ≤ k` guard on the equality clause is essential (see fidelity).
- *Reasoning:* characterises trees by a counting equality — a conceptual characterisation.
- *Fidelity:* ⚠ **statement repaired.** Read per-`k`, the book's equality clause is **false at `k = 2`** (`C₄` has `π₂ = 2 = 2·1³`); the Lean version guards it with `3 ≤ k`. Documented. See §C.

### Ex 8.4.4 — `numColorings_cycleGraph` (L2469, sorry)
**KEEP_CORE · high · reusable computation · Core/**
- *Source:* "`π_k(C_n) = (k-1)ⁿ + (-1)ⁿ(k-1)`."
- *Downstream:* prose-cited by `numColorings_wheel`.
- *Constants:* the closed form is exact.
- *Reasoning:* the second standard chromatic polynomial; input to the wheel formula and the canonical deletion–contraction worked example.
- *Fidelity:* stated over `ℤ` to accommodate `(-1)ⁿ`.

### Ex 8.4.5(a) — `numColorings_join_singleton` (L2501, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "`π_k(G ∨ K₁) = k·π_{k-1}(G)`."
- *Downstream:* prose-cited by 8.4.5(b), `wheel`.
- *Reasoning:* the apex/cone recursion for chromatic polynomials — a general reduction step.
- *Fidelity:* none.

### Ex 8.4.5(b) — `numColorings_wheel` (L2532, sorry)
**KEEP_CORE · medium · reusable computation · Core/**
- *Source:* "`π_k(W_n) = k(k-2)ⁿ + (-1)ⁿ k(k-2)`."
- *Downstream:* prose-cited by (a), `wheel`.
- *Constants:* exact closed form for a parameterised family.
- *Reasoning:* pure substitution of 8.4.4 into 8.4.5(a), so it adds little inference power — but it is a family formula (not a single value) and a standard reference entry.
- *Fidelity:* none.

### Ex 8.4.6 — `numColorings_eq_prod_components` (L2565, sorry)
**KEEP_CORE · high · reusable structural lemma · Core/**
- *Source:* "`π_k(G) = ∏ π_k(Gᵢ)` over the components."
- *Downstream:* prose-cited by `IsCritical.connected`, `numColorings_union_mul_inter`.
- *Reasoning:* multiplicativity over components is the first reduction any chromatic-polynomial computation performs.
- *Fidelity:* none.

### Ex 8.4.7 — `numColorings_union_mul_inter` (L2608, sorry)
**KEEP_CORE · high · reusable structural lemma · Core/**
- *Source:* "if `G ∩ H` is complete, `π_k(G ∪ H)π_k(G ∩ H) = π_k(G)π_k(H)`."
- *Downstream:* none yet.
- *Constants:* completeness of the overlap is the essential hypothesis.
- *Reasoning:* the clique-sum (gluing) formula — the second general reduction after 8.4.6.
- *Fidelity:* none.

### Ex 8.4.8 — `chromaticPolynomial_no_root_gt_card` (L2651, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (starred, L. Lovász) "no real root of `π_k(G)` exceeds `ν`."
- *Downstream:* none yet.
- *Constants:* `ν` is the sharp bound (roots at `0,…` up to `ν`).
- *Reasoning:* attributed and a genuine analytic statement about chromatic polynomials.
- *Fidelity:* none.

### Ex 8.5.1 — `mycielskiTower_isKCritical` (L2773, sorry)
**KEEP_CORE · high · structural theorem · Core/**
- *Source:* "each `G_k` in Mycielski's tower from `G₂ = K₂` is `k`-critical."
- *Downstream:* prose-cited by `mycielskiTower`.
- *Upstream:* Ex 8.1.7 (`K₂` is 2-critical) is the base case.
- *Reasoning:* the standard triangle-free-high-chromatic tower; the criticality strengthening is what makes it useful for building critical graphs of every order.
- *Fidelity:* none.

### Ex 8.5.2(a) — `descartes_construction` (L2824, sorry)
**KEEP_CORE · high · named construction · Core/**
- *Source:* (starred, B. Descartes) the inductive step producing girth-6 graphs of higher chromatic number.
- *Downstream:* prose-cited by (b), `exists_triangleFree_chromaticNumber_eq`.
- *Constants:* `6` (girth) and `C(kν, ν)` copies are the construction's data; `k ≥ 2` is the induction base.
- *Reasoning:* attributed, and the inductive engine of the headline existence theorem in (b).
- *Fidelity:* none.

### Ex 8.5.2(b) — `exists_chromaticNumber_ge_girth_six` (L2859, sorry)
**KEEP_CORE · high · headline existence theorem · Core/**
- *Source:* "for any `k ≥ 2` there is a `k`-chromatic graph of girth six."
- *Downstream:* prose-cited by (a), `exists_triangleFree_chromaticNumber_eq`.
- *Constants:* `6` is the girth achieved by this construction (the general "arbitrary girth" theorem is Erdős's probabilistic one, out of scope here).
- *Reasoning:* the theorem the section exists to prove — chromatic number is not a local property.
- *Fidelity:* stated as `(k : ℕ∞) ≤ χ(H)` rather than `=`; a slight weakening the induction needs, and documented.

### Ex 8.6.3 — `exists_isCanonicalColouring` (L2913, sorry)
**KEEP_CORE · high · bridge lemma · Core/**
- *Source:* "if `G` is `k`-vertex-colourable, `G` has a canonical `k`-vertex colouring."
- *Downstream:* prose-cited by `IsCanonicalColouring`.
- *Reasoning:* §8.6 calls this "easy to see" and then *relies on it* for the colouring algorithm; it is a genuine bridge from arbitrary colourings to the canonical form the section's algorithms consume.
- *Fidelity:* none.

---

## A.8 `PlanarGraphs.lean` — chapter 9 (7 declarations)

### Ex 9.3.3(a) — `not_both_card_edge_le_of_eleven_le` (L657, sorry)
**KEEP_CORE · medium · reusable arithmetic core · Core/**
- *Source:* "if `G` is a simple planar graph with `ν ≥ 11`, then `Gᶜ` is nonplanar."
- *Downstream:* prose-cited by `card_edgeFinset_add_card_edgeFinset_compl`.
- *Constants:* `11` is the **exact threshold** at which the Euler-bound counting argument closes (`2·(3ν-6) < C(ν,2)` first holds at `ν = 11`); `6` and `3` come from Euler's formula. None are example values.
- *Reasoning:* the arithmetic contradiction is the reusable part and is stated cleanly.
- *Fidelity:* ⚠ **this is not exercise 9.3.3(a) as stated** — the docstring says so. What is stated is the arithmetic core (`¬(ε(G)+6 ≤ 3ν ∧ ε(Gᶜ)+6 ≤ 3ν)`); "planar" never appears, so the actual exercise — that `Gᶜ` is nonplanar — is **not stated anywhere in the file**. See §C.

### Ex 9.4.1 — `bridge_inter_subset_cycle` (L703, sorry)
**KEEP_CORE · high · reusable structural lemma · Core/**
- *Source:* "two distinct bridges satisfy `V(B) ∩ V(B') ⊆ V(C)`."
- *Downstream:* none in code; the fact underpins the whole bridge apparatus of §9.4.
- *Reasoning:* the basic disjointness property of bridges; every bridge argument in the chapter assumes it.
- *Fidelity:* none.

### Ex 9.4.3(a)(i) — `exists_bridge_off_longest_cycle` (L974, sorry)
**KEEP_CORE · high · bridge lemma · Core/**
- *Source:* "for a longest cycle `C` in a nonhamiltonian connected `G`, some bridge `B` has `V(B) \ V(C) ≠ ∅`."
- *Downstream:* prose-cited 5×, notably by `chvatal_erdos_hamiltonian`.
- *Reasoning:* step (i) of the Chvátal–Erdős proof; a real dependency.
- *Fidelity:* none.

### Ex 9.4.3(a)(ii) — `succ_attachments_not_adj` (L1029, sorry)
**KEEP_CORE · high · bridge lemma · Core/**
- *Source:* "if `vᵢ`, `vⱼ` are attachments of `B`, then `v_{i+1}v_{j+1} ∉ E`."
- *Downstream:* prose-cited 5×.
- *Reasoning:* step (ii) of Chvátal–Erdős; the non-adjacency that generates the independent set.
- *Fidelity:* ⚠ **statement repaired — hypothesis added.** Without `hoff` (the bridge has a vertex off `C`) the statement is **false**; the docstring gives `K₅` as an explicit counterexample. The repair is correct and documented. See §C.

### Ex 9.4.3(b) — `chvatal_erdos_hamiltonian` (L1080, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (Chvátal, Erdős) "if `α ≤ κ`, then `G` is hamiltonian."
- *Downstream:* prose-cited 5×.
- *Constants:* none numeric beyond `3 ≤ ν`.
- *Reasoning:* one of the most-cited sufficient conditions for hamiltonicity; attributed.
- *Fidelity:* ⚠ `hν : 3 ≤ Fintype.card V` is **load-bearing and not in B&M** — `K₂` has `α = κ = 1` but is not hamiltonian in Mathlib's sense. A necessary repair, documented. See §C.

### Ex 9.6.4 — `lineGraph_colorable_three_of_isHamiltonian_of_three_regular` (L1134, sorry)
**KEEP_CORE · high · structural special case · Core/**
- *Source:* "every hamiltonian 3-regular graph has a Tait colouring."
- *Downstream:* none yet.
- *Constants:* `3` twice — cubic graphs and 3-edge-colourings; a **named structural class** (Tait colourings are defined only for cubic graphs).
- *Reasoning:* the positive half of the Tait-colouring story, of which Ex 9.6.7(b) is the negative half; both are needed to see the picture.
- *Fidelity:* none.

### Ex 9.6.7(b) — `exists_three_regular_two_connected_without_tait_colouring` (L1189, sorry)
**KEEP_EXAMPLE · high · counterexample · Examples/**
- *Source:* "Give an example of a 3-regular 2-connected graph with no Tait colouring."
- *Downstream:* prose-cited by `petersenGraph`, `vertexConnectivity`.
- *Upstream:* `PlanarGraphs.petersenGraph` — **honest** definition here, so not vacuous.
- *Constants:* `3`-regular and `2`-connected are the hypotheses being shown insufficient; the Petersen graph is the canonical witness.
- *Reasoning:* certifies that Ex 9.6.4's hamiltonicity hypothesis cannot be weakened to 2-connectivity. A witness, not an inference step.
- *Fidelity:* none.

---

## A.9 `DirectedGraphs.lean` — chapter 10 (27 declarations)

### Ex 10.1.1 — `card_orientations` (L797, sorry)
**KEEP_CORE · high · reusable computation · Core/**
- *Source:* "How many orientations does a simple graph have?" → `2^ε`.
- *Downstream:* prose-cited by `IsOrientationOf`, `arcCount`.
- *Constants:* `2` = two directions per edge, structural.
- *Reasoning:* the basic counting fact for orientations; needed by any probabilistic or averaging argument over orientations.
- *Fidelity:* the exercise poses a question; the Lean statement supplies the answer, which the docstring flags as part of what must be proved.

### Ex 10.1.2 — `sum_indegree_eq_arcCount` (L827, sorry)
**KEEP_CORE · high · fundamental lemma · Core/**
- *Source:* "`∑ d⁻(v) = ε = ∑ d⁺(v)`."
- *Downstream:* prose-cited by `arcCount`, `indegree`.
- *Reasoning:* the directed handshake — the counting identity every degree argument in the chapter opens with.
- *Fidelity:* both halves stated as a conjunction; faithful.

### Ex 10.1.3(a) — `exists_indegree_zero_of_acyclic` (L859, sorry)
**KEEP_CORE · high · fundamental lemma · Core/**
- *Source:* "a digraph with no directed cycle has `δ⁻ = 0`."
- *Downstream:* prose-cited 6× (`condensation`, `condensation_acyclic`, `exists_topological_ordering`, `exists_outdegree_zero_of_acyclic`, `exists_orientation_longest_directedPath_le`, `minIndegree`).
- *Reasoning:* the source vertex of a DAG; six downstream citers.
- *Fidelity:* none.

### Ex 10.1.3(b) — `exists_topological_ordering` (L895, sorry)
**KEEP_CORE · high · fundamental structure theorem · Core/**
- *Source:* "an acyclic digraph admits a vertex ordering with all arcs forward."
- *Downstream:* prose-cited 6×.
- *Existing equivalent:* none in Mathlib for this `Digraph` encoding.
- *Reasoning:* topological sort — arguably the single most reusable fact about DAGs.
- *Fidelity:* none.

### Ex 10.1.5(a)(i) — `converse_converse` (L924, sorry)
**KEEP_CORE · high · reusable API lemma · Core/**
- *Source:* "`D̆̆ = D`."
- *Downstream:* prose-cited 7× within the converse family.
- *Reasoning:* involutivity is what makes every "dualise the statement" argument work; the file uses the converse duality repeatedly (e.g. Ex 10.1.5(b)).
- *Fidelity:* none.

### Ex 10.1.5(a)(ii) — `converse_indegree` (L954, sorry)
**KEEP_CORE · high · reusable API lemma · Core/**
- *Source:* "`d^±_{D̆}(v) = d^∓_D(v)`."
- *Downstream:* prose-cited 7×; explicitly the route prescribed by Ex 10.1.5(b).
- *Reasoning:* the degree half of the converse duality.
- *Fidelity:* both halves stated as a conjunction; faithful.

### Ex 10.1.5(a)(iii) — `converse_reachable` (L985, sorry)
**KEEP_CORE · medium · reusable API lemma · Core/**
- *Source:* "`v` reachable from `u` in `D̆` iff `u` reachable from `v` in `D`."
- *Downstream:* prose-cited 7×.
- *Existing equivalent:* ⚠ possibly — the docstring says "Search Mathlib first: `Relation.reflTransGen_swap`… would close the goal". If that lemma exists, this is a thin `Digraph`-level wrapper.
- *Reasoning:* kept because the `Digraph.converse`/`Digraph.Reachable` wrapper is the form the rest of the file consumes. **Flagged for human review** (§E) pending the Mathlib check the docstring requests.
- *Fidelity:* none.

### Ex 10.1.5(b) — `exists_outdegree_zero_of_acyclic` (L1016, sorry)
**KEEP_CORE · high · fundamental lemma (dual) · Core/**
- *Source:* "deduce from 10.1.3(a) via (a)(ii) that an acyclic digraph has `δ⁺ = 0`."
- *Downstream:* prose-cited 7×.
- *Reasoning:* the sink counterpart of 10.1.3(a); both are needed (topological sort uses one, condensation arguments the other).
- *Fidelity:* none.

### Ex 10.1.6 — `exists_directedPath_length_ge_maxMinDegree` (L1051, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "a strict digraph contains a directed path of length ≥ `max{δ⁻, δ⁺}`."
- *Downstream:* prose-cited by `exists_directedCycle_length_ge`, `roy_gallai_directed_path`.
- *Constants:* the bound is sharp.
- *Reasoning:* the directed analogue of Ex 1.6.3, with the same reuse profile.
- *Fidelity:* ⚠ the docstring flags that the statement asks for **one** path realising the max, which is easy to get wrong.

### Ex 10.1.7 — `exists_directedCycle_length_ge` (L1086, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "strict with `max{δ⁻,δ⁺} = k > 0` ⇒ a directed cycle of length ≥ `k + 1`."
- *Downstream:* prose-cited by `ghouila_houri_directed_hamilton_cycle` and `GraphsAndSubgraphs.exists_long_cycle_of_minDegree`.
- *Constants:* `k + 1` sharp.
- *Reasoning:* directed analogue of Ex 1.7.3; feeds the chapter's Hamilton theorem.
- *Fidelity:* none.

### Ex 10.1.8 — `adjMatrix_pow_apply_eq_card_directedWalk` (L1126, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "the `(i,j)` entry of `Aᵏ` counts directed walks of length `k`."
- *Downstream:* prose-cited 4× (`adjMatrix`, `tournament_adjMatrix_isPrimitive_iff`, `tournament_adjMatrix_pow_pos`, and the undirected Ex 1.6.2).
- *Existing equivalent:* Mathlib has the **undirected** version only; the `Digraph` version is genuinely absent.
- *Reasoning:* unlike its undirected twin (which is dropped as a Mathlib alias), this one adds content, and three tournament results depend on it.
- *Fidelity:* ⚠ restated for a `0/1` matrix since `Digraph` has no arc multiplicities.

### Ex 10.1.9 — `condensation_acyclic` (L1164, sorry)
**KEEP_CORE · high · fundamental structure theorem · Core/**
- *Source:* "the condensation `D̂` contains no directed cycle."
- *Downstream:* prose-cited by `condensation`, `isUnilateral_iff_exists_spanning_directedWalk`, `tournament_diconnected_or_reorient_one`.
- *Reasoning:* the defining property of the condensation, and what makes the DAG machinery applicable to arbitrary digraphs.
- *Fidelity:* none.

### Ex 10.1.10 — `exists_balanced_orientation` (L1205, sorry)
**KEEP_CORE · high · reusable existence theorem · Core/**
- *Source:* "`G` has an orientation with `|d⁺(v) - d⁻(v)| ≤ 1` for all `v`."
- *Downstream:* prose-cited by `IsOrientationOf`, `outdegree`, and `Networks.isOrientable_iff_exists_partition` (Ex 11.5.5(a)).
- *Constants:* `1` is the exact best possible (parity).
- *Reasoning:* the Eulerian-orientation existence theorem; a cross-chapter dependency.
- *Fidelity:* stated as a two-sided `ℤ` bound to avoid `abs`; faithful.

### Ex 10.2.1 — `tournament_diconnected_or_reorient_one` (L1477, sorry)
**KEEP_CORE · high · structural theorem · Core/**
- *Source:* "every tournament is diconnected or becomes so after reorienting one arc."
- *Downstream:* prose-cited by `condensation`, `condensation_acyclic`, `toQuiver`.
- *Constants:* "one arc" is the exact bound.
- *Reasoning:* a sharp structural theorem about tournaments; the near-diconnectivity of tournaments is what makes the rest of §10.2 work.
- *Fidelity:* the reorientation is spelled out as an inline `Digraph.mk` with `if`s rather than via a `reorient` operation — verbose but faithful.

### Ex 10.2.2 — `isUnilateral_iff_exists_spanning_directedWalk` (L1520, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* (starred) "`D` is unilateral iff it has a spanning directed walk."
- *Downstream:* prose-cited by `IsUnilateral`.
- *Reasoning:* an iff-characterisation turning a quantified reachability property into the existence of one object — exactly the shape a prover wants.
- *Fidelity:* ⚠ the book means *walk*, not path; revisiting vertices is allowed. Correctly transcribed and flagged.

### Ex 10.2.3(a) — `tournament_maximal_directedPath_insert` (L1559, sorry)
**KEEP_CORE · high · bridge lemma · Core/**
- *Source:* "for a maximal non-Hamilton directed path in a tournament and `v` off it, some `i` has `(vᵢ,v)` and `(v,v_{i+1})` arcs."
- *Downstream:* prose-cited by `redei_directed_hamilton_path` and `moon_vertex_pancyclic`.
- *Reasoning:* the insertion lemma both Rédei's and Moon's theorems are built on — a genuine shared dependency.
- *Fidelity:* rendered over `List V` with `IsChain`; workable.

### Ex 10.2.5(a) — `chvatal_komlos_monotone_directedPath` (L1603, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (starred, Chvátal and Komlós) monotone directed paths from a chromatic hypothesis.
- *Downstream:* prose-cited by (b).
- *Constants:* `χ > mn` is the sharp threshold (the Gallai–Roy/Erdős–Szekeres product bound).
- *Reasoning:* attributed, sharp, and the general theorem behind Erdős–Szekeres.
- *Fidelity:* none.

### Ex 10.2.5(b) — `erdos_szekeres_of_chvatal_komlos` (L1645, sorry)
**KEEP_CORE · medium · named corollary · Core/**
- *Source:* (Erdős, Szekeres) monotone subsequences of length `m` or `n` in any sequence of `mn+1` distinct integers.
- *Downstream:* prose-cited by (a).
- *Existing equivalent:* ⚠ Mathlib has an Erdős–Szekeres proof in `Archive`, which **is not importable**; the docstring says so and the statement was restated locally.
- *Constants:* `mn + 1` is sharp.
- *Reasoning:* a famous named theorem, genuinely unavailable from Mathlib proper. **Flagged for human review** (§E) if the Archive version can be vendored instead.
- *Fidelity:* restated in `Finset` form rather than the Archive's; documented.

### Ex 10.2.6(a) — `exists_orientation_directedPath_le_maxDegree` (L1678, sorry)
**KEEP_CORE · high · corollary (Gallai–Roy) · Core/**
- *Source:* "using theorem 10.1 and corollary 8.1.2, `G` has an orientation with all directed paths of length ≤ `Δ`."
- *Downstream:* prose-cited by `exists_orientation_longest_directedPath_le`.
- *Constants:* `Δ` comes from `χ ≤ Δ + 1`; derived, not chosen.
- *Reasoning:* the Gallai–Roy direction relating colouring to orientations; a genuine cross-chapter theorem.
- *Fidelity:* ⚠ depends on chapter 8's corollary 8.1.2, out of module.

### Ex 10.3.1 — `dirac_of_ghouila_houri` (L1872, sorry)
**KEEP_EXAMPLE · medium · demonstration / cross-chapter derivation · Examples/**
- *Source:* "Show how theorem 4.3 can be deduced from theorem 10.4."
- *Downstream:* prose-cited by `associatedDigraph_pathEquiv`, `ghouila_houri_directed_hamilton_cycle`, `SimpleGraph.associatedDigraph`.
- *Existing equivalent:* **yes, locally** — the *statement* is Dirac's theorem, which already exists as `EulerHamilton.dirac_hamiltonian`.
- *Constants:* `3 ≤ ν` and `ν ≤ 2d(v)` are Dirac's, from the source.
- *Reasoning:* the exercise's content is the **deduction**, not the statement; as an API entry it duplicates a theorem the library already has. Its value is as a demonstration that the directed theorem subsumes the undirected one — a benchmark for the `associatedDigraph` machinery. That is `KEEP_EXAMPLE`, not core.
- *Fidelity:* faithful, but ⚠ its intended proof runs through `associatedDigraph_pathEquiv`, which is an opaque `sorry` definition (see below).

### Ex 10.3.2 — `exists_directedEulerTour_iff` (L1930, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "`D` has a directed Euler tour iff `D` is connected and `d⁺(v) = d⁻(v)` for all `v`."
- *Downstream:* prose-cited **8×** — the most-cited declaration in the module (de Bruijn results, `exists_arcDisjoint_directedPaths`, `arcsOf`, `IsDirectedEulerTour`).
- *Reasoning:* the directed Euler theorem; the whole §10.5 de Bruijn development is written against it. Retention is not in question.
- *Fidelity:* ⚠ **the `↔` is currently FALSE as stated.** The docstring gives the counterexample: an arc-free `D` with `card V ≥ 2` satisfies the left side vacuously (`Quiver.Path.nil` is an Euler tour with empty arc list) but fails the right side (not connected). Must be repaired before use. See §C.

### Ex 10.3.3 — `exists_arcDisjoint_directedPaths` (L1973, sorry)
**KEEP_CORE · high · reusable theorem · Core/**
- *Source:* "given the stated degree imbalance, there exist `l` arc-disjoint directed `(x,y)`-paths."
- *Downstream:* prose-cited by `arcsOf` and `Networks.unitCapacity_maxFlow_eq_arcDisjoint`.
- *Constants:* `l` is the imbalance, exact.
- *Reasoning:* the flow-decomposition lemma that Menger/max-flow arguments in chapter 11 consume.
- *Fidelity:* ⚠ two obstructions to the prescribed route (via Ex 10.3.2) are recorded in the docstring.

### Ex 10.3.4 — `exists_directed_odd_cycle` (L2015, sorry)
**KEEP_CORE · high · structural theorem · Core/**
- *Source:* (starred) "a diconnected digraph containing an odd cycle contains a directed odd cycle."
- *Downstream:* none yet.
- *Constants:* oddness is the parity invariant being transferred.
- *Reasoning:* a parity/structure transfer theorem; the underlying "well-defined parity of walks" argument is reusable.
- *Fidelity:* ⚠ the parity machinery has "no Mathlib counterpart for `Quiver.Path` and will have to be built".

### Ex 10.3.5 — `diconnected_iff_isKArcConnected_one` (L2053, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "a nontrivial digraph is diconnected iff it is 1-arc-connected."
- *Downstream:* prose-cited by `IsKArcConnected`, `associatedDigraph_isKArcConnected_iff`.
- *Constants:* `1` is the base of the arc-connectivity hierarchy.
- *Reasoning:* the base case identifying two definitions; a bridge lemma.
- *Fidelity:* none.

### Ex 10.3.6(a) — `associatedDigraph_pathEquiv` (L2099, `def`, sorry)
**DEFER · high · blocked (opaque construction) · Deferred/**
- *Source:* "there is a one-one correspondence between paths in `G` and directed paths in `D(G)`."
- *Downstream:* prose-cited 8×, including from `Networks.lean` (`menger_edge_graph`, `menger_vertex_graph`).
- *Reasoning:* the docstring is explicit: "⚠ **Defective: this definition has a `sorry` body.** It is declared `… ≃ … := sorry`, so the whole `Equiv` — *including its two functions* — is opaque… it could be any bijection at all, so it establishes nothing." Everything built on it (including `dirac_of_ghouila_houri` and two Menger statements) inherits the defect.
- *Fidelity:* the statement is right; the construction is absent. See §C and §E — this is the highest-leverage single repair in the module.

### Ex 10.3.6(b) — `associatedDigraph_isKArcConnected_iff` (L2147, sorry)
**KEEP_CORE · high · bridge lemma · Core/**
- *Source:* "`D(G)` is `k`-arc-connected iff `G` is `k`-edge-connected."
- *Downstream:* prose-cited 8×, including `Networks.menger_edge_graph` and `Networks.menger_vertex_graph` — it is the transfer principle that lets chapter 11 prove undirected Menger from the directed max-flow theorem.
- *Constants:* `k` is a parameter.
- *Reasoning:* a structural bridge with the widest cross-module reach in the file.
- *Fidelity:* ⚠ **the `↔` is FALSE on a one-vertex carrier** — the docstring works the counterexample out in full. Repair needed. See §C.

### Ex 10.5.2 — `exists_deBruijn_sequence` (L2283, sorry)
**KEEP_EXAMPLE · medium · construction / application · Examples/**
- *Source:* "for an `n`-letter alphabet there is a circular sequence of length `n⁴` containing every four-letter word."
- *Downstream:* none.
- *Constants:* `4` (word length), `n³`, `n⁴` — the book fixes the word length at `4`; `n` is a parameter.
- *Reasoning:* the headline application of the directed Euler theorem, but at one fixed word length; a prover cannot reuse the `k = 4` instance for any other `k`. **Flagged for human review** (§E): if §10.5 of the source develops de Bruijn sequences for general word length, this is a strong `GENERALIZE` candidate (parameterise `4` as `k`), and the file's own skeleton already builds the generalised de Bruijn digraph. Not recommended here because the source's coverage of the general case was not verified in this pass.
- *Fidelity:* ⚠ inherits the `exists_directedEulerTour_iff` defect through its step 4.

---

## A.10 `Networks.lean` — chapter 11 (12 declarations)

### Ex 11.1.2 — `sum_resultant_eq_fOut_sub_fIn` (L900, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "`∑_{v ∈ S}(f⁺(v) - f⁻(v)) = f⁺(S) - f⁻(S)`."
- *Downstream:* prose-cited 4× (`Network.fOut`, `Network.val`, `fOut_X_sub_fIn_X_eq_fIn_Y_sub_fOut_Y`, `val_eq_fOut_sub_fIn`).
- *Reasoning:* the telescoping identity every flow-conservation argument in the chapter starts from; the book itself warns the naive per-vertex version is false.
- *Fidelity:* stated over `ℤ`, which is **necessary** — the docstring notes the ℕ version is false because per-vertex subtraction truncates.

### Ex 11.1.3 — `fOut_X_sub_fIn_X_eq_fIn_Y_sub_fOut_Y` (L931, sorry)
**KEEP_CORE · high · reusable lemma · Core/**
- *Source:* "the resultant flow out of `X` equals the resultant flow into `Y`."
- *Downstream:* prose-cited 3×.
- *Upstream:* Ex 11.1.2.
- *Reasoning:* the well-definedness of "the value of a flow"; every max-flow statement depends on it.
- *Fidelity:* ⚠ the module's `X`/`x` source-set-versus-source-vertex seam is noted in the docstring.

### Ex 11.2.2 — `maxFlow_and_minCut_zero_of_no_path` (L1184, sorry)
**KEEP_CORE · medium · boundary case · Core/**
- *Source:* "if there is no directed `(x,y)`-path, max flow and min cut are both zero."
- *Downstream:* none yet.
- *Constants:* `0` is the degenerate value.
- *Reasoning:* the degenerate base case of max-flow min-cut. Boundary cases of major theorems are explicitly within the retention policy, and this one is the case a prover hits first when the network is disconnected.
- *Fidelity:* ⚠ inherits the `X`/`x` seam through theorem 11.1.

### Ex 11.2.3 — `isMinCut_union_inter` (L1218, sorry)
**KEEP_CORE · high · structural theorem · Core/**
- *Source:* "if `(S,S̄)` and `(T,T̄)` are minimum cuts, so are `(S∪T, …)` and `(S∩T, …)`."
- *Downstream:* none yet.
- *Reasoning:* the lattice structure of minimum cuts, whose content is **submodularity of the cut function** — a genuinely reusable inequality far beyond this exercise.
- *Fidelity:* none; the docstring notes it is unaffected by the module's `X`/`x` defect.

### Ex 11.3.1 — `revisedFlow_isFlow_and_val` (L1387, sorry)
**DEFER · high · vacuous · Deferred/**
- *Source:* "`f̂` given by (11.9) is a flow with `val f̂ = val f + ι(P)`."
- *Downstream:* prose-cited 3× including `maxFlow_iff_no_incrementing_path`.
- *Reasoning:* the docstring states "⚠ **Currently vacuous.** Both `N.revisedFlow` and `P.iota` have `sorry` bodies, so this statement relates two opaque constants and asserts nothing." The repair is spelled out in the definitions' docstrings (structural recursion over `IncPath`).
- *Fidelity:* faithful once the two definitions exist.

### Ex 11.4.1 — `minArcsSplit_eq_minVertices` (L1637, sorry)
**DEFER · high · vacuous · Deferred/**
- *Source:* "in theorem 11.6's proof, min arcs in `D'` = min vertices in `D`."
- *Downstream:* prose-cited by `menger_vertex_digraph`, `splitDigraph`.
- *Reasoning:* both `minArcsDestroyingDirectedPaths` and `minVerticesDestroyingDirectedPaths` are `:= sorry` **with all arguments `_`-ignored**, so both sides are the same opaque constant and the statement is trivially unfalsifiable.
- *Fidelity:* faithful once the two quantities are defined.

### Ex 11.4.3 — `maxSTVertexDisjointPaths_eq_minSTSeparator` (L1799, sorry)
**DEFER · high · vacuous · Deferred/**
- *Source:* "max vertex-disjoint `S`–`T` paths = min `S`–`T` separator."
- *Downstream:* prose-cited 3× including `dirac_k_vertices_on_cycle`.
- *Reasoning:* the set-to-set Menger theorem — genuinely core mathematics — but both sides are `:= sorry` with `_`-ignored arguments. The docstring notes both are "among the six **definable today**", so the block is shallow.
- *Fidelity:* ⚠ the intended proof changes carrier, so the statement's `G` and the theorem's `G` differ; recorded.

### Ex 11.4.4 — `dirac_k_vertices_on_cycle` (L1837, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (starred, Dirac) "if `G` is `k`-connected with `k ≥ 2`, any `k` vertices lie together on some cycle."
- *Downstream:* prose-cited by `maxSTVertexDisjointPaths`, Ex 11.4.3.
- *Constants:* `k ≥ 2` is essential (`k = 1` gives no cycle).
- *Reasoning:* attributed, and the canonical application of set-to-set Menger.
- *Fidelity:* none.

### Ex 11.5.2 — `not_realisable_54421` (L2041, sorry)
**KEEP_EXAMPLE · high · counterexample · Examples/**
- *Source:* "`p = q = (5,4,4,2,1)` is not realisable by a simple bipartite graph."
- *Downstream:* prose-cited by `RealisableBipartite`.
- *Constants:* the sequence `(5,4,4,2,1)` is **the specific witness** the book uses to show condition (11.16) is not sufficient — the numbers are the content and cannot be varied.
- *Reasoning:* a decisive counterexample certifying that the Gale–Ryser condition is stronger than the sum condition. Not an inference step.
- *Fidelity:* none. Likely `decide`-able at these fixed sizes.

### Ex 11.5.4(a) — `realisable_iff_reduced` (L2083, sorry)
**KEEP_CORE · high · reusable recursion (Gale–Ryser) · Core/**
- *Source:* (starred) the reduction step `(p,q)` realisable iff `(p',q')` realisable.
- *Downstream:* none yet.
- *Reasoning:* the recursive characterisation that makes bipartite degree-sequence realisability decidable; a genuine algorithmic inference step.
- *Fidelity:* ⚠ two departures from the book are flagged in the source comment — notably the construction of `q'`. See §C.

### Ex 11.5.5(a) — `isOrientable_iff_exists_partition` (L2122, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* (starred) "`G` is `(m,n)`-orientable iff there is a partition `(V₁,V₂)` with `|(m-n)(|V₁∩S| - |V₂∩S|)| ≤ |[S,S̄]|` for all `S`."
- *Downstream:* prose-cited 3× including Ex 11.5.5(b).
- *Upstream:* `DirectedGraphs.exists_balanced_orientation` (Ex 10.1.10).
- *Reasoning:* an iff-characterisation converting an orientation-existence question into a finite inequality; the shape a decision procedure needs.
- *Fidelity:* `abs` avoided by a two-sided bound — faithful. ⚠ needs an eulerian orientation from chapter 10.

### Ex 11.5.5(b) — `isOrientable_pred_succ` (L2159, sorry)
**KEEP_CORE · high · corollary · Core/**
- *Source:* "if `G` is `(m,n)`-orientable and `m > n`, it is `(m-1,n+1)`-orientable."
- *Downstream:* prose-cited 3×.
- *Constants:* the `±1` shift is the exact step; iterating it gives the full orientability interval.
- *Reasoning:* a monotonicity step that, applied repeatedly, characterises the whole set of orientable pairs.
- *Fidelity:* ⚠ `m - 1` in ℕ needs `1 ≤ m`, supplied by `hmn : n < m`.

---

## A.11 `CycleSpaceBondSpace.lean` — chapter 12 (13 declarations)

> This module is the most heavily blocked in the library: **8 of its 13 exercise
> declarations take a hypothesis whose predicate is `Prop := sorry`** (`IsSpanningTree`,
> `IsBasisMatrixOfTree`, `IsBasisMatrixOfTree'`, `IsConnectedDigraph`), so no caller
> could ever discharge them. Those are `DEFER`, uniformly and for the same reason.

### Ex 12.1.1(b) — `circulation_unique_of_restrict_compl` (L1317, sorry)
**DEFER · high · blocked (undischargeable hypothesis) · Deferred/**
- *Source:* "a circulation `f` is uniquely determined by `f | T̄`."
- *Downstream:* prose-cited by `basisMatrix_unique_of_restrict`, `potentialDiff_unique_of_restrict`.
- *Reasoning:* takes `hT : IsSpanningTree tail head T`, and `IsSpanningTree` is `Prop := sorry` — no caller can supply the hypothesis. The mathematics is core (it is what makes the tree-basis of the cycle space work), so this is a block, not a demotion.
- *Fidelity:* faithful.

### Ex 12.1.1(b) — `potentialDiff_unique_of_restrict` (L1347, sorry)
**DEFER · high · blocked · Deferred/** — the dual half ("`g` is determined by `g | T`"); same `IsSpanningTree` block. Prose-cited 2×. ⚠ its step 3 ("a spanning tree meets every bond") is itself an unstated lemma.

### Ex 12.1.2(a) — `basisMatrix_unique_of_restrict` (L1378, sorry)
**DEFER · high · blocked · Deferred/**
- *Source:* "`B` is uniquely determined by `B | T` and `C` by `C | T̄`."
- *Downstream:* prose-cited 4×.
- *Reasoning:* blocked on `IsSpanningTree`.
- *Fidelity:* ⚠ **only the `B` half of the book's statement is transcribed**; the `C` half is missing. When this is unblocked it is also a `GENERALIZE` candidate — state both conjuncts as the source does.

### Ex 12.1.2(b) — `basisMatrix_eq_restrict_mul` (L1413, sorry)
**DEFER · high · blocked and false as stated · Deferred/**
- *Source:* "`B = (B | T₁) B₁` for basis matrices of `𝓑` w.r.t. two spanning trees."
- *Downstream:* prose-cited 4×.
- *Reasoning:* blocked on `IsSpanningTree`, **and** the docstring records that the statement "**is therefore false**" as written because it omits `B₁ | T₁ = 1` (i.e. that `B₁` is the *tree*-`T₁` basis matrix, not an arbitrary basis matrix). See §C.
- *Fidelity:* ⚠ missing hypothesis.

### Ex 12.1.3 — `isBasisMatrix_deleteRow` (L1446, sorry)
**DEFER · high · blocked · Deferred/**
- *Source:* "deleting any one row of the incidence matrix of a connected digraph gives a basis matrix of `𝓑`."
- *Downstream:* prose-cited 4× including `matrix_tree_theorem` and Ex 12.2.1(b).
- *Reasoning:* takes `hconn : IsConnectedDigraph tail head`, which is `Prop := sorry`. The result itself is core — it is what makes `K` a basis matrix in the matrix-tree theorem.
- *Fidelity:* ⚠ the statement omits `Nonempty V`; noted in the docstring.

### Ex 12.2.1(a) — `isUnimodular_deleteRow` (L1477, sorry)
**KEEP_CORE · high · named theorem · Core/**
- *Source:* (starred) "a matrix obtained from `M` by deleting one row is unimodular."
- *Downstream:* prose-cited 4× including `matrix_tree_theorem`.
- *Upstream:* uses only `orientedIncMatrix` and `IsUnimodular`, **both honest definitions** — this statement is *not* blocked.
- *Reasoning:* the unimodularity fact the matrix-tree theorem's determinant computation rests on; starred in the source.
- *Fidelity:* ⚠ the statement lacks a connectivity hypothesis that the intended proof route may need; recorded.

### Ex 12.2.1(b) — `tau_eq_det_fromBlocks_K` (L1509, sorry)
**DEFER · high · blocked · Deferred/**
- *Source:* "`τ(G) = ± det [K; C]`."
- *Downstream:* prose-cited 4×.
- *Reasoning:* takes both `IsSpanningTree` and `IsBasisMatrixOfTree'`, both `Prop := sorry`.
- *Fidelity:* ⚠ no canonical row-reindexing exists, so an explicit `Equiv` argument `e` is threaded through — a formalisation artefact, not a book quantity.

### Ex 12.2.2(a) — `lapMatrix_eq_orientedIncMatrix_mul_transpose` (L1553, sorry)
**KEEP_CORE · high · fundamental identity · Core/**
- *Source:* "the conductance matrix satisfies `C = MM'` for any orientation."
- *Downstream:* prose-cited 5× including `matrix_tree_theorem`, Ex 12.2.2(b), and `GraphsAndSubgraphs.adjMatrix_sq_diag`.
- *Upstream:* `IsOrientationOf` → `IsUnderlyingGraph`, both **honest** — not blocked.
- *Existing equivalent:* Mathlib has `SimpleGraph.lapMatrix` but not this factorisation through an arbitrary orientation.
- *Reasoning:* the Laplacian factorisation — the single identity from which the matrix-tree theorem follows.
- *Fidelity:* ⚠ the identity requires looplessness and no parallel arcs; both noted.

### Ex 12.2.2(b) — `tau_eq_det_lapMatrix_deleteRowCol` (L1586, sorry)
**GENERALIZE · high · named theorem (Matrix–Tree) · Core/**
- *Source:* "**all** cofactors of the conductance matrix are equal to `τ(G)`."
- *Downstream:* prose-cited 5× including `matrix_tree_theorem`.
- *Upstream:* honest definitions only — not blocked.
- *Constants:* none; `y` is the deleted index.
- *Reasoning:* the Lean statement asserts only that the **principal `(y,y)`-minor** equals `τ`. The book asserts all cofactors are equal to `τ`, which is strictly stronger and is the form usually cited (it is what lets you delete *any* row and *any* column). The docstring flags the gap explicitly. This is recovering the source statement, not inventing a generalization.
- *Fidelity:* ⚠ principal minor only; the general-cofactor claim is absent.
- **Possible generalized form:** `∀ (i j : V), (τ : ℤ) = (-1)^(idx i + idx j) * ((G.lapMatrix ℤ).submatrix (delete row i) (delete col j)).det` — i.e. every cofactor, as the source states.

### Ex 12.2.3(a) — `isTotallyUnimodular_basisMatrixOfTree` (L1622, sorry)
**DEFER · high · blocked · Deferred/**
- *Source:* "any tree-basis matrix of `𝓑` or `𝓒` is totally unimodular."
- *Downstream:* prose-cited by Ex 12.2.3(b), `IsUnimodular`.
- *Reasoning:* the docstring says "⚠ Currently vacuous via `IsSpanningTree` and `IsBasisMatrixOfTree`".
- *Fidelity:* faithful once unblocked.

### Ex 12.2.3(b) — `incMatrix_isTotallyUnimodular_iff_isBipartite` (L1657, sorry)
**KEEP_CORE · high · structural characterisation · Core/**
- *Source:* "the incidence matrix of a simple graph is totally unimodular iff `G` is bipartite."
- *Downstream:* prose-cited by Ex 12.2.3(a), `IsUnimodular`.
- *Upstream:* the docstring notes "★ **Independent of every defective definition in this file** — it mentions only `SimpleGraph.incMatrix` and `IsBipartite`, both Mathlib."
- *Reasoning:* a clean iff-characterisation stated entirely in Mathlib vocabulary, connecting integer programming to bipartiteness. The highest-value unblocked item in the module.
- *Fidelity:* ⚠ this is the *unoriented* `0/1` incidence matrix of §1.3, not the oriented one; correctly flagged.

### Ex 12.2.4(a) — `det_fromBlocks_eq_tau_mod` (L1688, sorry)
**DEFER · high · blocked · Deferred/**
- *Source:* "over a field of characteristic `p`, `det [B; C] = ± τ(G) (mod p)`."
- *Downstream:* prose-cited 4×.
- *Reasoning:* takes `IsBasisMatrixOfTree` and `IsBasisMatrixOfTree'`, both `Prop := sorry`. The docstring adds that step 1 needs the *concrete* `{0, ±1}` entries, which "is a genuine constraint on how `IsBasisMatrixOfTree` is [defined]" — so the block is not merely mechanical: the eventual definition must be strong enough or **the statement is false**. See §C.
- *Fidelity:* faithful in intent.

### Ex 12.2.4(b) — `finrank_inf_pos_iff_dvd_tau` (L1727, sorry)
**KEEP_CORE · high · named characterisation · Core/**
- *Source:* (H. Shank) "over a field of characteristic `p`, `dim(𝓑_F ∩ 𝓒_F) > 0` iff `p ∣ τ(G)`."
- *Downstream:* prose-cited 4×.
- *Upstream:* `bondSpace`, `cycleSpace`, `tau` — all **honest** definitions; not blocked.
- *Constants:* `p` prime is a parameter; the divisibility is the exact criterion.
- *Reasoning:* an attributed, striking characterisation linking a linear-algebraic degeneracy to an arithmetic property of the spanning-tree count. Fully stateable today.
- *Fidelity:* ⚠ its step 1 must not be derived from orthogonality (which fails in characteristic `p`); noted.

---

## B. Summary table — all 226 exercise declarations

Legend: **C** = KEEP_CORE, **G** = GENERALIZE, **X** = KEEP_EXAMPLE, **D** = DEFER,
**R** = DROP_FROM_LIBRARY. `†` marks an entry with a correctness concern listed in §C.

### B.1 `GraphsAndSubgraphs.lean` (38)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 1.1.3 | `edgeCard_le_choose_two` | R | high |
| 1.2.2(a) | `iso_card_eq` | R | med |
| 1.2.5 | `nonempty_iso_iff` | C | med |
| 1.2.7 | `edgeCard_eq_choose_two_iff_top` | C | high |
| 1.2.8(a) | `completeBipartite_edgeCard` | C | high |
| 1.2.8(b) | `bipartite_edgeCard_le` | C | high |
| 1.2.10 | `hypercube` | C | high |
| 1.2.10 | `hypercube_card_vertices` | R † | high |
| 1.2.10 | `hypercube_edgeCard` | C | med |
| 1.2.10 | `hypercube_bipartite` | C | high |
| 1.2.11(b) | `selfComplementary_card_mod_four` | C | high |
| 1.3.1(a) | `incMatrix_col_sum` | R | high |
| 1.5.2 | `adjMatrix_sq_diag` | **G** | high |
| 1.4.1 | `exists_embedding_into_completeGraph` | R † | med |
| 1.4.2(a) | `induce_completeGraph` | C | med |
| 1.4.2(b) | `subgraph_bipartite` | **G** | med |
| 1.5.1 | `degree_bounds` | C | high |
| 1.5.3 | `regular_bipartite_card_eq` | C | high |
| 1.5.4 | `exists_two_same_degree` | X | med |
| 1.5.8 | `exists_bipartite_spanning_subgraph` | C | high |
| 1.5.10(a) | `lineGraph_card_vertices` | R | high |
| 1.5.10(a) | `lineGraph_edgeCard` | C | high |
| 1.6.1 | `exists_path_of_walk` | R | high |
| 1.6.2 | `card_walks_length_eq_adjMatrix_pow` | R | high |
| 1.6.3 | `exists_path_length_of_minDegree` | C | high |
| 1.6.4 | `connected_iff_forall_partition_edge` | C | high |
| 1.6.5(a) | `connected_of_edgeCard_gt` | C | high |
| 1.6.7 | `compl_connected_of_not_connected` | C | high |
| 1.6.8(a) | `components_deleteEdge` | **G** | high |
| 1.6.11 | `dist_triangle` | R † | high |
| 1.6.12 | `compl_diam_lt_of_diam_gt` | C | med |
| 1.6.14 | `exists_induced_path_of_connected_not_complete` | C | high |
| 1.7.1 | `edge_in_cycle_of_closed_trail` | C | high |
| 1.7.2 | `exists_cycle_of_minDegree_ge_two` | C | high |
| 1.7.3 | `exists_long_cycle_of_minDegree` | C | high |
| 1.7.4(a) | `girth_four_regular_card_ge` | C | high |
| 1.7.4(b) | `girth_five_regular_card_ge` | C | high |
| 1.7.6(a) | `exists_cycle_of_edgeCard_ge` | C † | high |

### B.2 `Connectivity.lean` (6)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 2.3.1(a) | `exists_isVertexCut_singleton_of_isBridge` | C | high |
| 3.1.2 | `edgeCard_ge_of_kEdgeConnected` | C | high |
| 3.1.3(a) | `vertexConnectivity_eq_minDegree_of_delta_ge` | C | high |
| 3.1.6 | `vertexConn_eq_edgeConn_of_threeRegular` | C | high |
| 3.2.1 | `two_edge_connected_iff_two_edge_disjoint_paths` | C | high |
| 3.3.2 | `hararyGraph_conn_eq` | D | high |

### B.3 `EulerHamilton.lean` (16)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 4.1.2 | `exists_eulerian_even_order_odd_size` | X | high |
| 4.1.4 | `even_degree_cycle_decomposition` | C | high |
| 4.1.5 | `odd_vertices_trail_cover` | C | high |
| 4.1.6 | `ore_extendable_tour_iff_forest` | D † | high |
| 4.2.1(a) | `nonhamiltonian_of_not_two_connected` | C | high |
| 4.2.1(b) | `nonhamiltonian_of_unbalanced_bipartite` | C | high |
| 4.2.3 | `hamiltonian_path_toughness` | C | high |
| 4.2.4 | `chvatal_hamiltonian_path` | C | high |
| 4.2.5 | `hamiltonian_path_of_self_complementary` | **G** | med |
| 4.2.6 | `chvatal_bipartite_hamiltonian` | D † | high |
| 4.2.8 | `erdos_hamiltonian` | C | high |
| 4.2.9 | `long_path_of_order_gt_two_minDegree` | C | high |
| 4.2.10 | `nash_williams_regular_hamiltonian` | C † | med |
| 4.2.11(a) | `hamiltonConnected_edge_bound` | C † | high |
| 4.2.11(b) | `exists_extremal_hamiltonConnected` | X † | high |
| 4.2.12 | `petersen_isHypohamiltonian` | D | high |

### B.4 `Matchings.lean` (28)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 5.1.1(a) | `cube_isPerfectMatching` | C † | med |
| 5.1.1(b) | `card_perfectMatching_completeGraph` | C | med |
| 5.1.1(b) | `card_perfectMatching_completeBipartite` | C | med |
| 5.1.2 | `isTree_subsingleton_perfectMatching` | C | high |
| 5.1.3 | `exists_regular_matchingFree` | X | high |
| 5.1.4 | `WinsFrom` | D | high |
| 5.1.4 | `first_player_wins_iff_no_perfect_matching` | D † | high |
| 5.1.5(a)(i) | `completeBipartite_one_factorable` | C | high |
| 5.1.5(a)(i) | `completeGraph_even_one_factorable` | C | high |
| 5.1.5(a)(ii) | `petersenGraph_not_one_factorable` | X | high |
| 5.1.5(c) | `exists_three_factor_of_minDegree` | C | high |
| 5.1.6 | `completeGraph_odd_two_factorable` | C | high |
| 5.2.1 | `mutilated_chessboard` | X | high |
| 5.2.2(a) | `bipartite_perfectMatching_iff` | C † | high |
| 5.2.2(b) | `exists_not_bipartite_hall_counterexample` | X | high |
| 5.2.3(a) | `regular_bipartite_one_factorable` | C | high |
| 5.2.3(b) | `regular_two_factorable` | C | high |
| 5.2.4 | `exists_sdr` | R | med |
| 5.2.5 | `konig_matrix` | C | high |
| 5.2.6(a) | `konig_ore_defect` | C | high |
| 5.2.6(b) | `exists_matching_card_eq_of_card_edges_gt` | C † | med |
| 5.2.8(a) | `doublyStochastic_card_eq` | C | med |
| 5.2.8(b) | `birkhoff_von_neumann` | R | high |
| 5.2.9 | `exists_common_coset_transversal` | C † | med |
| 5.3.2 | `perfectMatching_of_edgeConnected_regular` | C † | high |
| 5.3.3 | `isTree_perfectMatching_iff` | C | high |
| 5.3.4 | `berge_tutte_defect` | C | high |
| 5.3.5(b) | `perfectMatching_of_card_edges_gt` | C | high |

### B.5 `EdgeColourings.lean` (14)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 6.1.1 | `edgeChromaticNumber_completeBipartiteGraph` | X | med |
| 6.1.2 | `petersenGraph_edgeChromaticNumber` | D | high |
| 6.1.3(a) | `exists_regular_bipartite_supergraph` | C † | med |
| 6.1.6 | `exists_edge_colouring_all_represented_of_isBipartite` | C | high |
| 6.2.1 | `edgeChromaticNumber_completeGraph_odd` | C | high |
| 6.2.1 | `edgeChromaticNumber_completeGraph_even` | C | high |
| 6.2.2 | `edgeChromaticNumber_eq_maxDegree_add_one_of_regular_odd_card` | C | high |
| 6.2.3(a) | `edgeChromaticNumber_eq_maxDegree_add_one_of_card_edges_gt` | C | high |
| 6.2.3(b)(i) | `edgeChromaticNumber_subdivide_eq_maxDegree_add_one` | C | high |
| 6.2.3(b)(ii) | `edgeChromaticNumber_deleteEdges_eq_maxDegree_add_one` | C | high |
| 6.2.4(a) | `exists_regular_supergraph` | D † | med |
| 6.2.5 | `isHamiltonian_of_uniquely_three_edge_colourable` | C | high |
| 6.2.6(a) | `edgeChromaticNumber_boxProd_completeGraph_two` | C | high |
| 6.2.6(b) | `edgeChromaticNumber_boxProd` | C | high |

### B.6 `IndependentSetsCliques.lean` (27)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 7.2.1 | `ramseyNumber_comm` | C | high |
| 7.2.4(a) | `indepNum_composition_le` | C | high |
| 7.2.4(b) | `ramsey_product_lower` | C † | high |
| 7.2.4(c) | `abbott_lower_bound` | C | high |
| 7.2.5 | `grahamGraph_cliqueFree_six` | X | high |
| 7.2.5 | `grahamGraph_monochromatic_triangle` | X † | high |
| 7.2.6(a) | `generalisedRamsey_path_path` | X | high |
| 7.2.6(a) | `generalisedRamsey_path_cycle` | X | high |
| 7.2.6(a) | `generalisedRamsey_cycle_cycle` | X | high |
| 7.2.6(b) | `generalisedRamsey_tree_star` | C | high |
| 7.2.6(c) | `chvatal_tree_complete` | C | high |
| 7.3.1 | `nine_people_triangle` | X | high |
| 7.3.3(a) | `triangle_of_card_edgeFinset_gt` | C | high |
| 7.3.3(b) | `completeBipartite_triangle_free_extremal` | X | high |
| 7.3.3(c) | `triangle_of_not_bipartite_of_card_edgeFinset_gt` | C | high |
| 7.3.4(a) | `isContained_completeBipartite_two_of_sum_choose_gt` | C | high |
| 7.3.4(b) | `isContained_completeBipartite_two_of_card_edgeFinset_gt` | C | high |
| 7.3.4(c) | `card_unit_distance_pairs_le` | C | high |
| 7.3.5 | `isContained_completeBipartite_of_card_edgeFinset_gt` | C | high |
| 7.4.1 | `schurNumber_one` | X | high |
| 7.4.1 | `schurNumber_two` | X | high |
| 7.4.1 | `schurNumber_three` | C | high |
| 7.4.2(a) | `schurNumber_recursion` | C | high |
| 7.4.2(b) | `schurNumber_lower_bound` | C | high |
| 7.5.1(a) | `card_unitDistanceGraph_le_of_diam_one` | C | high |
| 7.5.1(b) | `exists_unitDistanceGraph_card_eq` | X † | high |
| 7.5.2 | `police_cars` | X † | med |

### B.7 `VertexColourings.lean` (38)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 8.1.1 | `chromaticNumber_ge_of_card_edges` | C | high |
| 8.1.2 | `chromaticNumber_le_five_of_odd_cycles_meet` | C | high |
| 8.1.3 | `welsh_powell` | C | high |
| 8.1.4(a) | `chromaticNumber_le_ceil_sqrt_two_mul_card_edges` | C † | high |
| 8.1.4(b) | `nordhaus_gaddum` | C | high |
| 8.1.5 | `szekeres_wilf` | C | high |
| 8.1.6 | `gallai_two_per_class` | C | high |
| 8.1.7 | `isKCritical_one_iff` | C | high |
| 8.1.7 | `isKCritical_two_iff` | C | high |
| 8.1.7 | `isKCritical_three_iff_odd_cycle` | C | high |
| 8.1.8 | `IsKCritical.not_uniquelyColorable_of_isVertexCut` | C | high |
| 8.1.9(a) | `IsCritical.neighborSet_not_subset` | C | high |
| 8.1.9(b) | `no_isKCritical_card_eq_succ` | C | high |
| 8.1.10(a) | `chromaticNumber_join` | C | high |
| 8.1.10(b) | `join_isCritical_iff` | C | high |
| 8.1.11 | `hajos_construction` | C | high |
| 8.1.12 | `exists_isKCritical_four` | C | med |
| 8.1.13(a) | `kainen` | C | high |
| 8.1.13(b) | `IsKCritical.edgeConnectivity_ge` | C | high |
| 8.2.1 | `brooks_iff_edge_bound` | C | high |
| 8.2.2 | `chromaticIndex_le_four_of_maxDegree_three` | C | high |
| 8.3.1 | `hasK4Subdivision_of_few_low_degree` | C † | high |
| 8.3.2(a) | `hasK4Subdivision_of_card_edges` | C | high |
| 8.3.2(b) | `exists_no_hasK4Subdivision_card_edges` | X | high |
| 8.4.2(a) | `chromaticPolynomial_coeff_card_sub_one` | C | high |
| 8.4.2(b) | `no_graph_chromaticPolynomial_eq` | X | high |
| 8.4.3(a) | `numColorings_of_isTree` | C | high |
| 8.4.3(b) | `numColorings_le_of_connected` | C † | high |
| 8.4.4 | `numColorings_cycleGraph` | C | high |
| 8.4.5(a) | `numColorings_join_singleton` | C | high |
| 8.4.5(b) | `numColorings_wheel` | C | med |
| 8.4.6 | `numColorings_eq_prod_components` | C | high |
| 8.4.7 | `numColorings_union_mul_inter` | C | high |
| 8.4.8 | `chromaticPolynomial_no_root_gt_card` | C | high |
| 8.5.1 | `mycielskiTower_isKCritical` | C | high |
| 8.5.2(a) | `descartes_construction` | C | high |
| 8.5.2(b) | `exists_chromaticNumber_ge_girth_six` | C | high |
| 8.6.3 | `exists_isCanonicalColouring` | C | high |

### B.8 `PlanarGraphs.lean` (7)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 9.3.3(a) | `not_both_card_edge_le_of_eleven_le` | C † | med |
| 9.4.1 | `bridge_inter_subset_cycle` | C | high |
| 9.4.3(a)(i) | `exists_bridge_off_longest_cycle` | C | high |
| 9.4.3(a)(ii) | `succ_attachments_not_adj` | C † | high |
| 9.4.3(b) | `chvatal_erdos_hamiltonian` | C † | high |
| 9.6.4 | `lineGraph_colorable_three_of_isHamiltonian_of_three_regular` | C | high |
| 9.6.7(b) | `exists_three_regular_two_connected_without_tait_colouring` | X | high |

### B.9 `DirectedGraphs.lean` (27)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 10.1.1 | `card_orientations` | C | high |
| 10.1.2 | `sum_indegree_eq_arcCount` | C | high |
| 10.1.3(a) | `exists_indegree_zero_of_acyclic` | C | high |
| 10.1.3(b) | `exists_topological_ordering` | C | high |
| 10.1.5(a)(i) | `converse_converse` | C | high |
| 10.1.5(a)(ii) | `converse_indegree` | C | high |
| 10.1.5(a)(iii) | `converse_reachable` | C | med |
| 10.1.5(b) | `exists_outdegree_zero_of_acyclic` | C | high |
| 10.1.6 | `exists_directedPath_length_ge_maxMinDegree` | C | high |
| 10.1.7 | `exists_directedCycle_length_ge` | C | high |
| 10.1.8 | `adjMatrix_pow_apply_eq_card_directedWalk` | C | high |
| 10.1.9 | `condensation_acyclic` | C | high |
| 10.1.10 | `exists_balanced_orientation` | C | high |
| 10.2.1 | `tournament_diconnected_or_reorient_one` | C | high |
| 10.2.2 | `isUnilateral_iff_exists_spanning_directedWalk` | C | high |
| 10.2.3(a) | `tournament_maximal_directedPath_insert` | C | high |
| 10.2.5(a) | `chvatal_komlos_monotone_directedPath` | C | high |
| 10.2.5(b) | `erdos_szekeres_of_chvatal_komlos` | C | med |
| 10.2.6(a) | `exists_orientation_directedPath_le_maxDegree` | C | high |
| 10.3.1 | `dirac_of_ghouila_houri` | X | med |
| 10.3.2 | `exists_directedEulerTour_iff` | C † | high |
| 10.3.3 | `exists_arcDisjoint_directedPaths` | C | high |
| 10.3.4 | `exists_directed_odd_cycle` | C | high |
| 10.3.5 | `diconnected_iff_isKArcConnected_one` | C | high |
| 10.3.6(a) | `associatedDigraph_pathEquiv` | D † | high |
| 10.3.6(b) | `associatedDigraph_isKArcConnected_iff` | C † | high |
| 10.5.2 | `exists_deBruijn_sequence` | X | med |

### B.10 `Networks.lean` (12)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 11.1.2 | `sum_resultant_eq_fOut_sub_fIn` | C | high |
| 11.1.3 | `fOut_X_sub_fIn_X_eq_fIn_Y_sub_fOut_Y` | C | high |
| 11.2.2 | `maxFlow_and_minCut_zero_of_no_path` | C | med |
| 11.2.3 | `isMinCut_union_inter` | C | high |
| 11.3.1 | `revisedFlow_isFlow_and_val` | D | high |
| 11.4.1 | `minArcsSplit_eq_minVertices` | D | high |
| 11.4.3 | `maxSTVertexDisjointPaths_eq_minSTSeparator` | D | high |
| 11.4.4 | `dirac_k_vertices_on_cycle` | C | high |
| 11.5.2 | `not_realisable_54421` | X | high |
| 11.5.4(a) | `realisable_iff_reduced` | C † | high |
| 11.5.5(a) | `isOrientable_iff_exists_partition` | C | high |
| 11.5.5(b) | `isOrientable_pred_succ` | C | high |

### B.11 `CycleSpaceBondSpace.lean` (13)

| Ex | Declaration | Rec | Conf |
|---|---|---|---|
| 12.1.1(b) | `circulation_unique_of_restrict_compl` | D | high |
| 12.1.1(b) | `potentialDiff_unique_of_restrict` | D | high |
| 12.1.2(a) | `basisMatrix_unique_of_restrict` | D † | high |
| 12.1.2(b) | `basisMatrix_eq_restrict_mul` | D † | high |
| 12.1.3 | `isBasisMatrix_deleteRow` | D | high |
| 12.2.1(a) | `isUnimodular_deleteRow` | C | high |
| 12.2.1(b) | `tau_eq_det_fromBlocks_K` | D | high |
| 12.2.2(a) | `lapMatrix_eq_orientedIncMatrix_mul_transpose` | C | high |
| 12.2.2(b) | `tau_eq_det_lapMatrix_deleteRowCol` | **G** | high |
| 12.2.3(a) | `isTotallyUnimodular_basisMatrixOfTree` | D | high |
| 12.2.3(b) | `incMatrix_isTotallyUnimodular_iff_isBipartite` | C | high |
| 12.2.4(a) | `det_fromBlocks_eq_tau_mod` | D † | high |
| 12.2.4(b) | `finrank_inf_pos_iff_dvd_tau` | C | high |

### B.12 Totals

Counts below were extracted mechanically from the rows of §B.1–§B.11 (226 rows parsed,
per-file counts matching the per-file headers exactly), not estimated.

| Recommendation | Count | Share |
|---|---:|---:|
| KEEP_CORE | 165 | 73.0% |
| KEEP_EXAMPLE | 25 | 11.1% |
| DEFER | 20 | 8.8% |
| DROP_FROM_LIBRARY | 11 | 4.9% |
| GENERALIZE | 5 | 2.2% |
| **Total** | **226** | **100%** |

Declarations carrying a `†` correctness concern (§C): **34**.

**Read the totals this way:** 84% of the exercise corpus (`KEEP_CORE` + `KEEP_EXAMPLE`)
is worth keeping in some form. Only 11 declarations — under 5% — are recommended for
removal from the library, and **all 11 are removable because Mathlib or this repo
already proves the same statement**, not because they are exercises. Nothing was
dropped for being an exercise, and nothing was dropped for containing a fixed number.

---

## C. Correctness concerns — reported separately from retention

These are statements that are **false, under-hypothesised, or not what the source
says**. Retention recommendations above are independent of this list; a `KEEP_CORE`
item appearing here should be repaired, not removed.

### C.1 Statements that are FALSE as written

| # | Declaration | Defect |
|---|---|---|
| 1 | `DirectedGraphs.exists_directedEulerTour_iff` (10.3.2) | The `↔` fails for an arc-free digraph with `card V ≥ 2`: `Quiver.Path.nil` is vacuously an Euler tour, so the LHS holds while the RHS (connected) fails. **Most-cited declaration in its module (8×).** |
| 2 | `DirectedGraphs.associatedDigraph_isKArcConnected_iff` (10.3.6(b)) | False on a one-vertex carrier: `IsKArcConnected 1` holds vacuously (no nonempty proper `S`), but `edgeConnectivity ⊥ = 0`. Consumed by two Menger statements in `Networks.lean`. |
| 3 | `CycleSpaceBondSpace.basisMatrix_eq_restrict_mul` (12.1.2(b)) | Omits `B₁ ∣ T₁ = 1`; without it any other basis matrix is a counterexample. The docstring states "As stated the theorem is therefore **false**". |
| 4 | `EulerHamilton.ore_extendable_tour_iff_forest` (4.1.6) | Docstring: "⚠ **The statement is false as written.**" Missing the book's `Nontrivial` + eulerian hypotheses. |
| 5 | `GraphsAndSubgraphs.exists_cycle_of_edgeCard_ge` (1.7.6(a)) | False for empty `V`; needs `[Nonempty V]`. |
| 6 | `EulerHamilton.nash_williams_regular_hamiltonian` (4.2.10) | Book requires `k ≥ 1`; omitted. At `k = 0` it claims a one-vertex graph is hamiltonian, which Mathlib rejects (a Hamilton cycle needs length ≥ 3). |
| 7 | `EulerHamilton.hamiltonConnected_edge_bound` (4.2.11(a)) | Book requires `ν ≥ 4`; omitted. False at `ν = 3`. |
| 8 | `EulerHamilton.exists_extremal_hamiltonConnected` (4.2.11(b)) | Hypothesis is `3 ≤ ν`; the book requires `4 ≤ ν`. |

### C.2 Statements likely unprovable in the chosen encoding

| # | Declaration | Concern |
|---|---|---|
| 9 | `EdgeColourings.exists_regular_supergraph` (6.2.4(a)) | The book's construction needs **multi-edges**, which `SimpleGraph` cannot express; and `↪g` is an *induced* embedding, forbidding the padding edges the construction adds. |
| 10 | `EdgeColourings.exists_regular_bipartite_supergraph` (6.1.3(a)) | Same `↪g`-is-induced concern; the docstring says it "would make the statement false. Worth checking carefully before proving." |
| 11 | `CycleSpaceBondSpace.det_fromBlocks_eq_tau_mod` (12.2.4(a)) | Requires `IsBasisMatrixOfTree` to force `{0, ±1}` entries. Since that predicate is `Prop := sorry`, the statement's truth depends on a definition that does not exist yet — "with[out] it this statement is false". |

### C.3 Deliberate, documented repairs (statement ≠ source, correctly)

These are **not** defects — they are repairs of source statements that are false in
Lean. They are listed so the divergence is auditable.

| Declaration | Repair |
|---|---|
| `VertexColourings.chromaticNumber_le_ceil_sqrt_two_mul_card_edges` (8.1.4(a)) | added `1 ≤ ε`; book's version false for the edgeless graph |
| `VertexColourings.numColorings_le_of_connected` (8.4.3(b)) | added `3 ≤ k` to the equality clause; false at `k = 2` (`C₄`) |
| `VertexColourings.hasK4Subdivision_of_few_low_degree` (8.3.1) | added `4 ≤ ν`; book's version false on tiny carriers |
| `PlanarGraphs.succ_attachments_not_adj` (9.4.3(a)(ii)) | added `hoff`; `K₅` is a counterexample without it |
| `PlanarGraphs.chvatal_erdos_hamiltonian` (9.4.3(b)) | added `3 ≤ ν`, not in B&M; `K₂` is a counterexample |
| `Matchings.doublyStochastic_card_eq` (5.2.8(a)) | restated for rectangular matrices; the literal book statement is vacuous in Mathlib's typing |

### C.4 Fidelity gaps — the Lean statement says less than the source

| Declaration | Gap |
|---|---|
| `PlanarGraphs.not_both_card_edge_le_of_eleven_le` (9.3.3(a)) | **The actual exercise is not stated anywhere.** What is stated is the arithmetic core; the word "planar" never appears and the conclusion "`Gᶜ` is nonplanar" is absent. |
| `GraphsAndSubgraphs.exists_embedding_into_completeGraph` (1.4.1) | Weakened to `G ≤ completeGraph V`, i.e. `le_top`; the book's isomorphism-onto-a-subgraph content is gone. |
| `GraphsAndSubgraphs.hypercube_card_vertices` (1.2.10) | Does not mention `hypercube` at all — it is a fact about the carrier type. |
| `GraphsAndSubgraphs.adjMatrix_sq_diag` (1.5.2) | Only the `A²` half of a two-part book statement. → **GENERALIZE** |
| `GraphsAndSubgraphs.subgraph_bipartite` (1.4.2(b)) | Only the same-carrier spanning case. → **GENERALIZE** |
| `CycleSpaceBondSpace.basisMatrix_unique_of_restrict` (12.1.2(a)) | Only the `B` half of a two-part book statement. |
| `CycleSpaceBondSpace.tau_eq_det_lapMatrix_deleteRowCol` (12.2.2(b)) | Only the principal minor; the book claims **all** cofactors. → **GENERALIZE** |
| `EulerHamilton.hamiltonian_path_of_self_complementary` (4.2.5) | Part (a), the general theorem, is not stated. → **GENERALIZE** |
| `EulerHamilton.chvatal_bipartite_hamiltonian` (4.2.6) | Docstring: "best-effort and does not faithfully match" the source. |
| `Matchings.exists_matching_card_eq_of_card_edges_gt` (5.2.6(b)) | Asks for cardinality **exactly** `k`; the argument yields **at least** `k`. |
| `Matchings.bipartite_perfectMatching_iff` (5.2.2(a)) | `hcov : X ∪ Y = univ` added with no counterpart in the source. |
| `Matchings.perfectMatching_of_edgeConnected_regular` (5.3.2) | `hν : Even ν` appears unused by the intended argument. |
| `Matchings.cube_isPerfectMatching` (5.1.1(a)) | `2 ≤ k` is stronger than the `1 ≤ k` the argument needs. |
| `Matchings.first_player_wins_iff_no_perfect_matching` (5.1.4) | "first player has a winning strategy" rendered as `∃ v₀, ¬ WinsFrom G {v₀} v₀` — reading flagged as uncertain. |
| `Matchings.exists_common_coset_transversal` (5.2.9) | The two conclusions rendered as `Function.Bijective` of coset maps — rendering flagged as needing review. |
| `Networks.realisable_iff_reduced` (11.5.4(a)) | Two departures from the book flagged in the source comment, notably the construction of `q'`. |
| `IndependentSetsCliques.grahamGraph_monochromatic_triangle` (7.2.5) | `χ` is total on all of `Sym2 _`, a stronger hypothesis than colouring only the edges. |
| `IndependentSetsCliques.exists_unitDistanceGraph_card_eq` (7.5.1(b)) | The Reuleaux construction is natural for odd `n`; the signature demands all `n ≥ 3`. |

### C.5 Missing supporting lemmas that the stated results silently require

| Consumer | Missing fact |
|---|---|
| `IndependentSetsCliques.ramsey_product_lower` (7.2.4(b)) | `(G[H])ᶜ ≅ Gᶜ[Hᶜ]` — "true but not obvious", not stated in the file |
| `Matchings.mutilated_chessboard` (5.2.1) | "a bipartite graph with unequal sides has no perfect matching" — "**does not exist in this file**" |
| `IndependentSetsCliques.abbott_lower_bound` (7.2.4(c)) | `r(3,3) = 6`; only `6 ≤ r(3,3)` is available |
| `Trees.connected_two_non_cutVertices` / `Trees.tree_card_edgeFinset` | component-count monotonicity `H ≤ K → ω(K) ≤ ω(H)` — the generalization proposed for Ex 1.6.8(a) |
| `IndependentSetsCliques.card_unit_distance_pairs_le` (7.3.4(c)) | "two distinct points have at most two common unit-distance neighbours" — not in Mathlib |

---

## D. Structural issues found while triaging (not per-declaration)

### D.1 `petersenGraph` is defined four times, twice opaquely

| Site | Carrier | Body |
|---|---|---|
| `EdgeColourings.lean:310` | `Fin 10` | `:= sorry` |
| `EulerHamilton.lean:1915` | `Fin 10` | `:= sorry` |
| `Matchings.lean:341` | `{s : Finset (Fin 5) // s.card = 2}` | honest (Kneser) |
| `PlanarGraphs.lean:525` | `{s : Finset (Fin 5) // s.card = 2}` | honest (Kneser) |

Consequence: `petersenGraph_edgeChromaticNumber` (6.1.2) and `petersen_isHypohamiltonian`
(4.2.12) are **vacuous**, while `petersenGraph_not_one_factorable` (5.1.5(a)(ii)) and
`exists_three_regular_two_connected_without_tait_colouring` (9.6.7(b)) are not — even
though 6.1.2's intended proof cites 5.1.5(a)(ii). The two honest definitions are also
duplicates of each other. Consolidating to one shared definition unblocks two `DEFER`
entries at a stroke and removes a cross-module inconsistency.

### D.2 `hypercube` and `cube` are the same graph, defined twice

`GraphsAndSubgraphs.hypercube` (L321) and `Matchings.cube` (L301) both have
`Adj x y := ∃! i, x i ≠ y i` on `Fin k → Bool`. Four theorems are stated about the
first and one about the second. They should be one definition.

### D.3 Two incompatible spellings of the component count

`Trees.numComponents` uses `Nat.card H.ConnectedComponent`;
`GraphsAndSubgraphs.components_deleteEdge` (Ex 1.6.8(a)) uses
`Fintype.card G.ConnectedComponent`. They agree over a `Fintype` carrier, but the
mismatch means the exercise cannot be applied to the theorem that cites it without a
transfer step. Unify before proving either.

### D.4 Name shadowing

`SimpleGraph.dist_triangle` (Ex 1.6.11) shadows the metric-space `dist_triangle` inside
`namespace SimpleGraph`. Since the declaration is recommended for removal as a Mathlib
duplicate anyway, this resolves itself.

### D.5 Cross-module dependencies that are not imports

Several exercises are blocked purely because the module that proves their prerequisite
is not imported: `Matchings.exists_three_factor_of_minDegree` (needs
`EulerHamilton.dirac_hamiltonian`), `EdgeColourings.edgeChromaticNumber_completeGraph_even`
(needs `Matchings`), `IndependentSetsCliques.completeBipartite_triangle_free_extremal`
(needs `GraphsAndSubgraphs.completeBipartite_edgeCard`),
`DirectedGraphs.exists_orientation_directedPath_le_maxDegree` (needs `VertexColourings`).
These are import-graph problems, not mathematical ones, and were **not** treated as
grounds for `DEFER`.

---

## E. Must be reviewed by a human before any action

Ordered by consequence.

1. **`DirectedGraphs.exists_directedEulerTour_iff` (Ex 10.3.2) is false.** It is the
   most-cited declaration in its module (8 citers, including the entire de Bruijn
   development). The repair — almost certainly adding a nonempty-arc-set or
   nontriviality condition — changes every downstream statement's hypotheses. Decide the
   repair before anyone starts proving against it.

2. **`DirectedGraphs.associatedDigraph_pathEquiv` (Ex 10.3.6(a)) is an opaque
   `Equiv := sorry`.** Eight declarations cite it, two of them (`Networks.menger_edge_graph`,
   `Networks.menger_vertex_graph`) are chapter-11 headline theorems. As the docstring
   says, "it could be any bijection at all, so it establishes nothing." Highest-leverage
   single repair in the library.

3. **`petersenGraph` duplication (§D.1).** Two opaque copies and two honest copies of the
   same graph, with a proof dependency running from an opaque copy to an honest one.
   Someone must choose the canonical definition and carrier.

4. **The eight `CycleSpaceBondSpace` `DEFER`s all hinge on four `Prop := sorry`
   predicates** (`IsSpanningTree`, `IsBasisMatrixOfTree`, `IsBasisMatrixOfTree'`,
   `IsConnectedDigraph`). Defining those four unblocks 8 of the module's 13 exercises.
   `det_fromBlocks_eq_tau_mod` additionally constrains what `IsBasisMatrixOfTree` must
   say (§C.2 #11) — so the definitions must be designed with that statement in hand, not
   written first and patched later.

5. **`Networks` has four `:= sorry` quantities with `_`-ignored arguments**
   (`minArcsDestroyingDirectedPaths`, `minVerticesDestroyingDirectedPaths`,
   `maxSTVertexDisjointPaths`, `minSTSeparator`). Two exercises equate pairs of them,
   which is currently unfalsifiable. The docstrings say all are "definable today".

6. **`PlanarGraphs.not_both_card_edge_le_of_eleven_le` (Ex 9.3.3(a))** is filed under an
   exercise it does not state. Either restate the real exercise (`ν ≥ 11 ⇒ Gᶜ nonplanar`)
   and demote this to a private helper, or relabel it. Provenance is currently misleading.

7. **`Matchings.exists_sdr` (Ex 5.2.4) — DROP is a judgement call.** It is a verbatim
   Mathlib alias, but the SDR phrasing is a genuinely different retrieval surface for an
   automated prover working in set-system rather than graph language. If the project
   wants that surface, keep it and mark it explicitly as a Mathlib re-export.

8. **`EdgeColourings.edgeChromaticNumber_completeBipartiteGraph` (Ex 6.1.1) — EXAMPLE vs
   CORE.** Theorem 6.1 (König) subsumes it, but Theorem 6.1 is blocked on the Euler chain
   and this exercise is reachable now via an explicit colouring. Whether build-order
   pragmatics justify a core slot is a project decision.

9. **`VertexColourings.exists_isKCritical_four` (Ex 8.1.12) — CORE vs EXAMPLE.** Its
   content is a construction (which would say `Examples/`), but its *statement* records a
   sharp existence spectrum with a real gap at `n = 5` (which says `Core/`). Classified
   `KEEP_CORE` here; reasonable people will differ.

10. **`IndependentSetsCliques.police_cars` (Ex 7.5.2)** — the recorded proof plan is
    broken (six sectors have diameter `6√3 ≈ 10.39 > 9`). The statement may well be true,
    but nobody should start proving it against the plan as written.

11. **`DirectedGraphs.converse_reachable` (Ex 10.1.5(a)(iii))** — the docstring asks for a
    Mathlib search (`Relation.reflTransGen_swap`) that was not completed. If that lemma
    exists, this becomes a candidate `DROP` alongside the other aliases.

12. **`DirectedGraphs.erdos_szekeres_of_chvatal_komlos` (Ex 10.2.5(b))** — Mathlib's
    `Archive` has Erdős–Szekeres but is not importable. Confirm the local restatement is
    the intended long-term answer rather than vendoring the Archive proof.

13. **`DirectedGraphs.exists_deBruijn_sequence` (Ex 10.5.2)** — potential `GENERALIZE` to
    arbitrary word length `k`. Not recommended here because §10.5's coverage of the
    general case was not verified. Someone with the book open should decide.

---

## F. Proposed file organization

**Implemented in pass 3 — see §G.5 for the one forced deviation.** The layout below is
what now exists on disk; `TCSlib/GraphTheory/README.md` documents it for readers.

```
TCSlib/GraphTheory/
├── Core/                    12 modules, one per chapter — THE RETRIEVAL SURFACE
│   ├── GraphsAndSubgraphs.lean   definitions, numbered theorems, and the exercises
│   ├── Connectivity.lean         carrying reusable inference steps, sharp thresholds,
│   ├── Trees.lean                bridge lemmas or structural characterisations
│   ├── EulerHamilton.lean        (165 KEEP_CORE + the 4 GENERALIZE additions)
│   ├── Matchings.lean
│   ├── EdgeColourings.lean
│   ├── IndependentSetsCliques.lean
│   ├── VertexColourings.lean
│   ├── PlanarGraphs.lean
│   ├── DirectedGraphs.lean
│   ├── Networks.lean
│   └── CycleSpaceBondSpace.lean
│
├── Examples/                9 modules — 20 declarations
│   │                        witnesses, counterexamples, worked applications
│   ├── GraphsAndSubgraphs.lean (1)   Matchings.lean (4)      EulerHamilton.lean (2)
│   ├── EdgeColourings.lean (1)       IndependentSetsCliques.lean (6)
│   ├── VertexColourings.lean (2)     PlanarGraphs.lean (1)
│   └── DirectedGraphs.lean (2)       Networks.lean (1)
│
├── Tests/                   1 module — 5 declarations
│   └── IndependentSetsCliques.lean   exact small values: r(P₄,P₄)=5, r(P₄,C₄)=5,
│                                     r(C₄,C₄)=6, s₁=2, s₂=5
│
├── Deferred/                7 modules — 20 declarations
│   │                        vacuous or undischargeable; ⚠ never cite these
│   ├── CycleSpaceBondSpace.lean (8)  Networks.lean (3)   EulerHamilton.lean (3)
│   ├── EdgeColourings.lean (2)       Matchings.lean (2)  Connectivity.lean (1)
│   └── DirectedGraphs.lean (1)
│
├── ExtractionArchive/
│   └── MathlibDuplicates.md          12 removed declarations, full source preserved
│
└── README.md                         layout, build command, aggregator blocker
```

Each `Examples/`, `Tests/` and `Deferred/` module imports **exactly one** `Core/`
chapter. Grouping is by chapter rather than by role because 12 declaration names are
defined in multiple chapters, so a role-based file spanning chapters cannot compile —
see §G.5.

Three properties this layout gives:

1. **`Core/` is the retrieval surface.** An automated prover indexes `Core/` only, so it
   never retrieves `r(P₄,P₄) = 5` or `mutilated_chessboard` when working on a general
   goal — while those results remain in the build and remain provable.
2. **`Deferred/` keeps blocked statements visible without letting them look usable.**
   Every one of the 20 carries an undischargeable hypothesis or an opaque constant; in
   `Core/` they are traps.
3. **`ExtractionArchive/` preserves provenance for the 12 drops.** Per the brief, the
   source record is not deleted — the manifest keeps the exercise number, the book
   statement, the Lean signature, and the superseding Mathlib name, so the extraction is
   auditable and the decision reversible.

**Sequencing suggestion.** Do not start the reorganisation with the file moves. The
highest-value work is the five items in §E.1–§E.5: they unblock most of the 20 `DEFER`s, fix two
false theorems with 8 citers each, and eliminate the `petersenGraph` fork. The
`Core/Examples/Tests/Deferred` split is worth doing after that, when the `DEFER` set has
shrunk and will not need re-partitioning.

---

---

## G. Implementation status (pass 2)

The recommendations that imply an edit to a declaration were applied in place.
`lake build TCSlib` passes after every change; no proof broke, because no dropped
declaration had a single Lean-code reference (§0.1).

### G.1 Applied — 12 removals

The 11 `DROP_FROM_LIBRARY` entries of §B, **plus Ex 1.5.2** (see §G.4), were removed
from their modules. Their full source — book statement, complete docstring, verbatim
Lean declaration — is preserved in
`TCSlib/GraphTheory/ExtractionArchive/MathlibDuplicates.md`, together with the
superseding Mathlib name for each. `TCSlib/GraphTheory` is **untracked by git**, so
the archive is the only record; every removal is reversible by pasting the block back.

`GraphsAndSubgraphs.lean` 1429 → 1246 lines; `Matchings.lean` 2403 → 2306 lines.

### G.2 Applied — 4 generalizations

| Exercise | Change |
|---|---|
| 1.4.2(b) | kept `subgraph_bipartite`; **added** `induce_bipartite` and `subgraph_induce_bipartite` (the book's "subgraph" = drop edges *and* vertices). Both proved, one line each, via `Colorable.of_embedding (Embedding.induce s)`. |
| 1.6.8(a) | **added** `card_connectedComponent_le_of_le : H ≤ K → Nat.card K.ConnectedComponent ≤ Nat.card H.ConnectedComponent`, the standalone monotonicity lemma `Trees.lean` asks for by name; the exercise is retained as the single-edge instance and its skeleton now cites the new lemma. |
| 4.2.5 | **added** `hamiltonian_path_of_degree_dominates_compl` — part (a), which the book states and deduces (b) from, but which had no declaration. Part (b) retained and now points at it. |
| 12.2.2(b) | kept the principal-minor form; **added** `tau_eq_lapMatrix_cofactor`, the book's "all cofactors" statement. |

In every case the exercise as originally stated was **kept** and the general form added
alongside — nothing was silently replaced by a stronger statement.

### G.3 Applied — 8 correctness repairs (§C.1)

| Exercise | Repair |
|---|---|
| 1.7.6(a) | `[Nonempty V]` added (was false on an empty carrier) |
| 4.1.6 | `[Nontrivial V]` and `hG : G.IsEulerianGraph` added, restoring the book's hypotheses |
| 4.2.10 | `hk : 1 ≤ k` added (was false at `k = 0`) |
| 4.2.11(a) | `hν : 4 ≤ Fintype.card V` added (was false at `ν = 3`) |
| 4.2.11(b) | `3 ≤ ν` corrected to `4 ≤ ν`, so it matches the bound whose sharpness it certifies |
| 10.3.2 | connectivity moved from the right-hand side of the `↔` into a hypothesis `hconn`. Both counterexamples are killed; no strengthening of the left side would have worked. Matches the shape of this library's undirected `euler_tour_iff_no_odd_degree`. |
| 10.3.6(b) | `[Nontrivial V]` added (was false on a one-vertex carrier) |
| 12.1.2(b) | `hB₁` strengthened from `IsBasisMatrix` to `IsBasisMatrixOfTree`, the repair its own docstring specified |

Each repaired docstring now records what changed and why, so the divergence from B&M
stays auditable.

### G.4 One triage verdict corrected during implementation

**Ex 1.5.2 `adjMatrix_sq_diag`: GENERALIZE → DROP_FROM_LIBRARY.** §A.1 recommended
generalizing it on the ground that the book covers both `MMᵀ` and `A²` while only the
`A²` half was transcribed, and that the `MMᵀ` half "is not in Mathlib". **That ground
was wrong** — Mathlib proves it verbatim as
`SimpleGraph.incMatrix_mul_transpose_diag`. With both halves available from Mathlib,
completing the transcription would have produced a declaration made entirely of
aliases, so the correct verdict under this document's own duplicate rule is `DROP`.
It was archived and removed. Revised totals: **165 → 164 KEEP_CORE-equivalent**,
**11 → 12 DROP**, **5 → 4 GENERALIZE**.

### G.5 Applied in pass 3 — the file reorganisation

Done on request, ahead of the §E repairs that §F recommended sequencing it after. The
`DEFER` partition may therefore need revisiting once §E lands.

**45 declarations moved** out of the chapter files: 20 → `Examples/`, 5 → `Tests/`,
20 → `Deferred/`. The 12 chapter files moved to `Core/`. Verified mechanically:
603 declarations before, 603 after, **none lost, none gained, none duplicated**. All
29 modules build.

**One deviation from §F's sketch, forced by a real blocker.** §F proposed *role-based*
destination files (`Examples/Counterexamples.lean`, `Examples/Witnesses.lean`, …).
Those cannot be built: **12 declaration names are defined in more than one chapter**,
all in `namespace SimpleGraph` — `IsVertexCut` ×5, `IsEdgeCut` ×4, `petersenGraph` ×4,
`vertexConnectivity` ×3, `edgeConnectivity` ×3, `join` ×3, plus `IsCutVertex`,
`subdivide`, `numComponents`, `degreeSequence`, `DegreeMajorised`, `IsCovering`. A
role-based file must import several chapters at once and fails with
`environment already contains …`.

This was latent before the move only because **no chapter file imported any other** —
every module was standalone, so the clashes never met. They are not new, and they are
§D.1/§D.2/§D.3 seen from a different angle.

Destination files are therefore **chapter-based**, each importing exactly one `Core/`
chapter. That sidesteps the clash and preserves what the layout was for: `Core/` is a
clean retrieval surface, `Deferred/` is visibly separate. Regrouping by role is a
mechanical follow-up once the 12 names are consolidated.

**There is also no `TCSlib/GraphTheory.lean` aggregator, for the same reason** — one
was written, failed to compile on `SimpleGraph.IsEdgeCut`, and was removed. The build
command and the full blocker table are in `TCSlib/GraphTheory/README.md`.

Note this raises the priority of §D.1/§D.2: consolidating the 12 duplicated definitions
is now the gate on both a role-based layout and any aggregator. It needs mathematical
decisions, not renaming — `petersenGraph` has two carriers *and* two `:= sorry` copies,
and `numComponents` is `Nat.card` in `Trees` but `Fintype.card` in chapter 1.

### G.6 Deliberately NOT done

- **The 13 items in §E.** Each needs a human decision (which `petersenGraph` is
  canonical, whether to vendor Mathlib's Archive Erdős–Szekeres, EXAMPLE-vs-CORE
  judgement calls). Two of them — §E.1 and §E.2's *statements* — were repaired above
  where the repair was forced; the design questions remain open.
- **Filling any `sorry`.** No proof was written. The library still has 208-odd `sorry`s
  and that was not this pass's job.
- **§C.2, §C.4, §C.5.** Statements *likely* unprovable in the chosen encoding, the
  remaining fidelity gaps, and the missing supporting lemmas were left alone: each
  needs a modelling decision (multi-edges for 6.2.4(a), what "subgraph" means for the
  `↪g` cases) rather than a mechanical edit.

---

*Pass 1 (triage) modified no files under `TCSlib/`. Pass 2 applied §G.1–§G.3; `lake
build TCSlib` passes.*


