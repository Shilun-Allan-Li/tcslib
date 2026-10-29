# GraphTheory — outstanding issues found during the annotation pass

Scope: chapters 3–6 (`Connectivity`, `EulerHamilton`, `Matchings`, `EdgeColourings`).
Chapters 1–2 and 7–12 have **not** been audited; absence from this list means
"not looked at", not "clean".

Every item below was found while rewriting docstrings and is **recorded only** —
no code was changed. Each is also noted in the relevant declaration's docstring;
this file is the index.

Line numbers are as of the annotation pass and will drift.

---

## A. False or unprovable as stated — fix before proving

These are not "hard", they are wrong. A proof attempt will fail or, worse,
succeed against a statement that does not say what the book says.

### A1. `ore_extendable_tour_iff_forest` — **false**
`EulerHamilton.lean:1354` (Ex 4.1.6*)

The book's hypotheses "let `G` be nontrivial and eulerian" were dropped from the
signature.

*Verified counterexample* (compiled, not merely argued): `G = ⊤` on `Bool`,
`v = true`.
- RHS holds — `G - v` is one vertex, hence acyclic.
- LHS fails — instantiating at `p := Walk.nil` demands an Euler tour based at
  `true`; `Walk.IsEulerian.even_degree_iff` forces every degree even for a
  *closed* Eulerian walk, but `deg(true) = 1`.

**Fix:** add `(hG : G.IsEulerianGraph)`.

### A2. `nash_williams_regular_hamiltonian` — false at `k = 0`
`EulerHamilton.lean:1771` (Ex 4.2.10)

Book says `k ≥ 1`; the signature omits it. At `k = 0` the claim is that the
one-vertex graph is hamiltonian — false in Mathlib, where a cycle needs length
≥ 3.

**Fix:** add `(hk : 1 ≤ k)`.

### A3. `hamiltonConnected_edge_bound` — false at `ν = 3`
`EulerHamilton.lean:1818` (Ex 4.2.11a)

Book says `ν ≥ 4`; the signature omits it. At `ν = 3`, `⊤` is
Hamilton-connected with `2ε = 6`, but the claim demands `3ν + 1 = 10`.

**Fix:** add `(hν : 4 ≤ Fintype.card V)`.

### A4. `exists_extremal_hamiltonConnected` — false at `ν = 3`
`EulerHamilton.lean:1866` (Ex 4.2.11b)

Signature has `3 ≤ ν`; book requires `ν ≥ 4`. At `ν = 3` the only
Hamilton-connected graph is `⊤` with `2ε = 6`, while the conclusion demands
`2ε ∈ {10, 11}`.

**Fix:** strengthen `hν` to `4 ≤ ν`.

### A5. `optimal_of_perfectMatching_equalitySubgraph` — `sorry` **inside the type**
`Matchings.lean:1087` (Thm 5.5)

The `Hom.ofLE` argument carries `(by sorry : equalitySubgraph w G l ≤ G)`. Until
that is discharged the statement does not yet mean what it should.

**Fix:** immediate from the first conjunct of `equalitySubgraph`'s `Adj`.

---

## B. Opaque definitions — theorems about them are unprovable, not just unproved

A `def := sorry` elaborates to a constant with no defining equations. Nothing
downstream can be proved until it is filled.

| Declaration | Blocks |
|---|---|
| `Connectivity.lean:1304` `hararyGraph` | Thm 3.3, `hararyGraph_edgeCard`, Ex 3.3.2 |
| `EulerHamilton.lean:1915` `petersenGraph` | `petersen_isHypohamiltonian` (Ex 4.2.12) |
| `EdgeColourings.lean:310` `petersenGraph` | `petersenGraph_edgeChromaticNumber` (Ex 6.1.2) |

**The two Petersen stubs are avoidable.** `Matchings.lean:341` already defines it
properly as the Kneser graph on `{s : Finset (Fin 5) // s.card = 2}` — a better
carrier than `Fin 10`, since vertex-transitivity cuts the case analysis. The
obstacle is purely organisational: neither file imports the other. Moving the
definition to a shared module beats writing a third copy.

`CycleSpaceBondSpace.lean` has 8 further `def := sorry` blocking 18 of its 29
theorems; see the separate note in that file's header.

---

## C. Statement fidelity — verify against the book before proving

Not known to be false, but the Lean form does not obviously say what the book
says. Proving these as written may not establish the exercise.

### C1. `chvatal_bipartite_hamiltonian`
`EulerHamilton.lean:1635` (Ex 4.2.6*)

The outline supplied no signature and the current form differs from the book in
at least two ways: the book's bound is `m ≤ ν/4` (i.e. `2m ≤ |X|`) where the Lean
`hcond` uses strict `2 * m < X.card`; and the book's second condition is on the
single entry `d_{ν/2}` where the Lean form uses a counting condition over `X`.

### C2. `exists_common_coset_transversal`
`Matchings.lean:2141` (Ex 5.2.9)

States `Function.Bijective` of maps into `Set H` rather than onto the set of
cosets, so the codomain is far larger than intended. The file already flagged the
shape as provisional.

### C3. `IsUniquelyEdgeColourable`
`EdgeColourings.lean:269` (Ex 6.2.5)

Rendered as "differ by a permutation of colours", which is equivalent to the
book's "induce the same partition" **only when every colour is used**. With `k`
exceeding the number of classes the two diverge.

**Fix (small, strictly better):** state it as the partition directly —
`∀ C C', ∀ e f, (C e = C f ↔ C' e = C' f)`. This also makes Ex 6.2.5's proof
cleaner, since it removes the need to argue that all three classes are nonempty.

---

## D. Trivial sorries — quick wins

### D1. Structure proof-fields (8 sorries, all one- or two-liners)

These are **not** opaque: the `Adj` field is fully defined, so downstream results
about them are already provable. Only `symm`/`loopless` are stubbed.

| Declaration | `symm` | `loopless` |
|---|---|---|
| `Matchings.lean:301` `cube` | `∃!` transport across `Ne.symm` | `x i ≠ x i` is false |
| `Matchings.lean:341` `petersenGraph` | `Disjoint.symm` | a 2-set is not disjoint from itself |
| `Matchings.lean:374` `gridGraph` | disjunction swap + `Or.symm` | `n + 1 = n` is false |
| `Matchings.lean:978` `equalitySubgraph` | `G.symm` + `Sym2.eq_swap` + `add_comm` | `G.loopless` |

### D2. Termination proof
`Matchings.lean:1329` `WinsFrom` — the `decreasing_by` is `sorry`. A third
species of `sorry`: the definition is usable, but the measure is unverified.
Discharged by `Finset.card_lt_card` on `visited ⊂ insert v visited`.

### D3. Hypotheses stronger than needed (harmless, but misleading)

- `Matchings.lean:1130` `cube_isPerfectMatching` has `2 ≤ k`; `1 ≤ k` suffices
  for the flip-first-coordinate matching.
- `Matchings.lean:2191` `perfectMatching_of_edgeConnected_regular` never uses its
  `Even (Fintype.card V)` under the argument the book indicates.

---

## E. Missing shared infrastructure — highest leverage

### E1. Degree-≤2 structure lemma ⭐
**"A graph with every degree ≤ 2 is a disjoint union of paths and cycles."**

Not in Mathlib. Required by:
- `Matchings.lean` `berge_maximum_matching` (Thm 5.1) — the load-bearing theorem
  of §5.1, which Hall's book-route also depends on;
- `EdgeColourings.lean` `exists_rebalanced_matchings` (Lem 6.3) — the book itself
  says "as in the proof of theorem 5.1";
- `Matchings.lean` `isTree_subsingleton_perfectMatching` would need it too, if
  proved via symmetric difference rather than leaf induction.

Proving this once, in a shared module, is the single highest-value missing piece
across chapters 5–6.

### E2. Colouring ↔ matching-partition bridge ⭐
**"The colour classes of a proper edge colouring are matchings, and conversely."**

The partition view is how §6.1 defines a proper colouring, but it is stated
nowhere. Required by `EdgeColourings.lean`'s Thm 6.3, Ex 6.1.2, Ex 6.2.3(a) and
both halves of Ex 6.2.6 — and it is also what `Matchings.lean`'s Ex 5.1.5
(1-factorability) needs.

Also remedies **E3**: `EdgeColourings.lean` uses two incompatible colouring
encodings — raw `G.edgeSet → Fin k` for §6.1's machinery (`IsRepresentedAt`,
`IsOptimalEdgeColouring`) and Mathlib's `G.lineGraph.Coloring (Fin k)` for every
`χ'` statement. Nothing converts between them.

### E4. Existence of an optimal edge colouring
`EdgeColourings.lean` — `IsOptimalEdgeColouring` is a static extremal condition;
that an optimal colouring *exists* follows from finiteness of
`G.edgeSet → Fin k` but is stated nowhere. Both Thm 6.1 and Vizing need it.

### E5. Edge-boundary ⇒ bridge
"An odd component whose edge boundary has size 1 yields a cut edge." Needed by
`Matchings.lean`'s Cor 5.4 (Petersen) and Ex 5.3.2.

---

## F. Duplication and organisation

- The connectivity API is duplicated across the directory, textually identical
  each time, so a change to one must be mirrored by hand:

  | Definition | Files |
  |---|---|
  | `IsVertexCut` | Connectivity, EulerHamilton, VertexColourings, IndependentSetsCliques, PlanarGraphs (**5**) |
  | `vertexConnectivity` | Connectivity, EulerHamilton, PlanarGraphs, Networks (**4**) |
  | `edgeConnectivity` | Connectivity, DirectedGraphs, Matchings, Networks, VertexColourings (**5**) |

  Note the sets differ — e.g. `Matchings` redefines `edgeConnectivity` but not
  `vertexConnectivity`, and `EulerHamilton` the reverse — so this is not a single
  block that can be lifted wholesale without checking each site.
- **`subdivide`** exists in two mutually-incompatible forms: `Connectivity.lean`
  (takes `e : Sym2 V`, raw structure) and `EdgeColourings.lean:237` (takes
  `u v : V` with `G.Adj u v`, built from `deleteEdges`/`sum`/`fromEdgeSet`).
  `EdgeColourings.lean` proves **nothing** about its version, which is the bulk
  of the work in Ex 6.2.3(b)(i).
- **Three Petersen graphs** — see §B.
- No file in `TCSlib/GraphTheory/` imports another. Every cross-chapter
  dependency noted in the docstrings is currently unsatisfiable as written.

---

## G. Content lost to the `SimpleGraph` model — not fixable here

Recorded so nobody spends time "fixing" them. The Lean statements are true; they
just no longer say what the exercise says, because the book works with loopless
**multigraphs** and `SimpleGraph` forces multiplicity `μ = 1`.

- `EdgeColourings.lean:1134` Ex 6.1.5 (`Δ = 3 ⇒ χ' ≤ 4`) — a genuine theorem for
  multigraphs; for simple graphs it is a one-line corollary of Vizing.
- `EdgeColourings.lean:1536` Ex 6.2.4(b) (Shannon's `χ' ≤ 3Δ/2`) — Vizing's
  `χ' ≤ Δ + 1` is already stronger for every `Δ ≥ 2`.
- General Vizing `Δ ≤ χ' ≤ Δ + μ` — not statable at all; dropped by the file.
- `EulerHamilton.lean` Cor 4.1 and Ex 4.1.5 both hinge on "add a new edge joining
  the two odd-degree vertices", which is a **no-op in `SimpleGraph`** when the
  pair is already adjacent. This is a modelling gap, not labour, and it blocks
  both proofs.
- `Matchings.lean:301` `cube` duplicates `GraphsAndSubgraphs.lean:257`
  `hypercube` (defined there via `fromRel` rather than as a raw structure); equal
  but not definitionally so. This one is a plain duplication rather than a
  modelling loss — listed here only because it is the same family of problem.

Note also `EdgeColourings.lean:1491` Ex 6.2.4(a): the *statement* is fine and
true (every graph with max degree `Δ` is an induced subgraph of a `Δ`-regular
graph), but the book's two-copy construction needs multi-edges to close a
deficiency `> 1` and so does not transfer. That is a proof-time note, not a
defect.

---

## H. Induced-embedding hazard

Mathlib's `↪g` is a `RelEmbedding` — it demands
`H.Adj (f a) (f b) ↔ G.Adj a b`, i.e. an **induced** embedding, not merely a
subgraph inclusion. Three statements in the repo use it:

- `GraphsAndSubgraphs.lean` `exists_embedding_into_completeGraph` — was **false**
  as originally stated (`Nonempty (G ↪g completeGraph V)` forces `G = ⊤`);
  corrected during the proving pass to `G ≤ completeGraph V`, with a compiled
  counterexample recorded at the site. **Already fixed.**
- `EdgeColourings.lean:1090` Ex 6.1.3(a) and `:1491` Ex 6.2.4(a) — statements are
  true, but any padding construction must never add an edge between two images of
  `G`-vertices. The two-disjoint-copies shape respects this; "add edges within
  `G`" does not.

---

## Suggested order of attack

1. **§A** — five one-line signature fixes. A false statement is worse than a
   stubbed one, and A1/A5 are actively misleading.
2. **§D1–D2** — 9 trivial sorries, no dependencies.
3. **§C3** — restate `IsUniquelyEdgeColourable`; 2 lines, strictly better.
4. **§F** — move `petersenGraph` (and the connectivity API) to a shared module;
   add the imports. Unblocks §B's two stubs without new mathematics.
5. **§E1–E2** — the two shared lemmas. Real work, but they unblock the most.
6. Only then the chapter theorems themselves.
